"""币安 Portfolio Margin 网关：统一交易账户，按实际市场分流公共行情。"""

import csv
import hashlib
import hmac
import re
from copy import copy
from datetime import datetime, timedelta
from decimal import Decimal
from enum import Enum
from pathlib import Path
from threading import Lock, RLock
from time import monotonic, time
from urllib.parse import urlencode

from requests.exceptions import SSLError

from vnpy.api.rest import Request, RestClient
from vnpy.api.websocket import WebsocketClient
from vnpy.event import Event, EventEngine
from vnpy.trader.constant import Direction, Exchange, Interval, Offset, OrderType, Product, Status
from vnpy.trader.event import EVENT_TIMER
from vnpy.trader.gateway import BaseGateway
from vnpy.trader.object import (
    AccountData,
    BarData,
    CancelRequest,
    ContractData,
    HistoryRequest,
    OrderData,
    OrderRequest,
    PositionData,
    SubscribeRequest,
    TickData,
    TradeData,
)
from vnpy.trader.setting import binance_account_main
from vnpy.trader.utility import TZ_INFO, GetFilePath, error_monitor, extract_vt_symbol, get_symbol_mark, is_target_contract

REST_HOST = "https://papi.binance.com"
WEBSOCKET_TRADE_HOST = "wss://fstream.binance.com/pm/ws/"
PUBLIC_REST_HOSTS = {
    Exchange.BINANCE: "https://api.binance.com",
    Exchange.BINANCEF: "https://dapi.binance.com",
    Exchange.BINANCES: "https://fapi.binance.com",
}
PUBLIC_PATHS = {
    Exchange.BINANCE: "/api/v3",
    Exchange.BINANCEF: "/dapi/v1",
    Exchange.BINANCES: "/fapi/v1",
}
MARKET_NAMES = {
    Exchange.BINANCE: "margin",
    Exchange.BINANCEF: "cm",
    Exchange.BINANCES: "um",
}
FUTURES_EXCHANGES = (Exchange.BINANCEF, Exchange.BINANCES)
BUSINESS_EXCHANGES = {"CM": Exchange.BINANCEF, "UM": Exchange.BINANCES}
DATA_HOSTS = {
    (Exchange.BINANCE, "all"): "wss://stream.binance.com:9443/stream",
    (Exchange.BINANCEF, "all"): "wss://dstream.binance.com/stream",
    (Exchange.BINANCES, "public"): "wss://fstream.binance.com/public/stream",
    (Exchange.BINANCES, "market"): "wss://fstream.binance.com/market/stream",
}
STATUS_BINANCEONE2VT = {
    "NEW": Status.NOTTRADED,
    "PENDING_NEW": Status.SUBMITTING,
    "PARTIALLY_FILLED": Status.PARTTRADED,
    "FILLED": Status.ALLTRADED,
    "CANCELED": Status.CANCELLED,
    "REJECTED": Status.REJECTED,
    "EXPIRED": Status.CANCELLED,
    "EXPIRED_IN_MATCH": Status.CANCELLED,
}
ORDERTYPE_VT2BINANCEONE = {
    OrderType.LIMIT: ("LIMIT", "GTC"),
    OrderType.MARKET: ("MARKET", ""),
    OrderType.FAK: ("LIMIT", "IOC"),
    OrderType.FOK: ("LIMIT", "FOK"),
}
ORDERTYPE_BINANCEONE2VT = {v: k for k, v in ORDERTYPE_VT2BINANCEONE.items()}
DIRECTION_VT2BINANCEONE = {Direction.LONG: "BUY", Direction.SHORT: "SELL"}
DIRECTION_BINANCEONE2VT = {v: k for k, v in DIRECTION_VT2BINANCEONE.items()}
INTERVAL_VT2BINANCEONE = {Interval.MINUTE: "1m", Interval.HOUR: "1h", Interval.DAILY: "1d"}
TIMEDELTA_MAP = {
    Interval.MINUTE: timedelta(minutes=1),
    Interval.HOUR: timedelta(hours=1),
    Interval.DAILY: timedelta(days=1),
}
CLOSE_OFFSETS = {Offset.CLOSE, Offset.CLOSETODAY, Offset.CLOSEYESTERDAY}
TERMINAL_STATUSES = {Status.ALLTRADED, Status.CANCELLED, Status.REJECTED}


class Security(Enum):
    NONE = 0
    SIGNED = 1
    API_KEY = 2


def generate_datetime(timestamp: int | float) -> datetime:
    """币安所有接口时间戳均为毫秒，不依赖数值位数推断单位。"""
    return datetime.fromtimestamp(float(timestamp) / 1000, TZ_INFO)


def format_number(value: float) -> str:
    """避免数量/价格出现科学计数法，不擅自修改用户委托精度。"""
    return format(Decimal(str(value)), "f")


def is_true(value) -> bool:
    return value is True or value == "true"


def get_order_type(order_type: str, time_in_force: str = "GTC") -> OrderType | None:
    if order_type in {"MARKET", "LIQUIDATION"}:
        return OrderType.MARKET
    if order_type == "LIMIT_MAKER":
        return OrderType.LIMIT
    if order_type == "LIMIT" and time_in_force in {"GTX", "GTD"}:
        return OrderType.LIMIT
    return ORDERTYPE_BINANCEONE2VT.get((order_type, time_in_force))


def local_orderid(symbol: str, exchange: Exchange, client_orderid: str) -> str:
    """交易所客户端编号只在对应市场/交易对内唯一，vnpy 编号必须隔离。"""
    return f"{MARKET_NAMES[exchange]}:{symbol}:{client_orderid}"


def client_orderid(symbol: str, exchange: Exchange, orderid: str) -> str:
    return str(orderid).removeprefix(f"{MARKET_NAMES[exchange]}:{symbol}:")


class BinanceOneGateway(BaseGateway):
    """
    币安统一账户，仅支持实盘、合约单向持仓和全仓模式。

    BINANCE 为统一账户全仓杠杆钱包的现货交易，默认自动借币/还款；
    BINANCEF 为币本位永续/交割合约，BINANCES 为 USDT/USDC 永续。
    """

    default_setting = {"key": "", "secret": "", "server": ["REAL"], "host": "", "port": 0}
    exchanges = [Exchange.BINANCE, Exchange.BINANCEF, Exchange.BINANCES]
    get_file_path = GetFilePath()

    def __init__(self, event_engine: EventEngine):
        super().__init__(event_engine, "BINANCEONE")
        self.orders: dict[str, OrderData] = {}
        self.order_lock = RLock()
        self.trade_ws_api = BinanceOneTradeWebsocketApi(self)
        self.market_ws_api = BinanceOneDataWebsocketApi(self)
        self.rest_api = BinanceOneRestApi(self)
        self.recording_list = [
            vt_symbol for vt_symbol in self.get_file_path.recording_list
            if is_target_contract(vt_symbol, self.gateway_name)
        ]
        self.history_contract = copy(self.recording_list)
        self.leverage_contract = copy(self.recording_list)
        self.query_count = 0
        self.query_functions = [self.query_account, self.query_position, self.query_order]
        self.history_status = True
        self.publish_status = True
        self.book_trade_status = False
        self.connected = False

    def connect(self, log_account: dict | None = None) -> None:
        if self.connected:
            return
        if not log_account:
            log_account = binance_account_main
        # 禁止将普通合约测试网冒充统一账户，也绝不从测试配置回退到实盘。
        if log_account.get("server") != "REAL":
            self.write_log("BINANCEONE未配置统一账户测试网，仅接受明确的REAL配置，未建立任何连接")
            return
        key, secret = log_account.get("key", ""), log_account.get("secret", "")
        if not key or not secret:
            self.write_log("BINANCEONE连接失败：统一账户API key/secret不能为空")
            return
        host = log_account.get("host", "")
        port = int(log_account.get("port", 0))
        self.account_file_name = log_account["account_file_name"]
        self.connected = True
        self.rest_api.connect(key, secret, "REAL", host, port)
        self.market_ws_api.connect(host, port, "REAL")
        self.event_engine.register(EVENT_TIMER, self.process_timer_event)
        self.event_engine.register(EVENT_TIMER, self.query_rest_data)
        if self.history_status:
            self.event_engine.register(EVENT_TIMER, self.query_history)

    def subscribe(self, req: SubscribeRequest) -> None:
        self.market_ws_api.subscribe(req)
        if req.exchange == Exchange.BINANCE:
            self.rest_api.push_spot_position(req.symbol)

    def send_order(self, req: OrderRequest) -> str:
        return self.rest_api.send_order(req)

    def cancel_order(self, req: CancelRequest) -> Request | None:
        return self.rest_api.cancel_order(req)

    def query_position(self) -> None:
        self.rest_api.query_position()

    def query_account(self) -> None:
        self.rest_api.query_account()

    def query_order(self) -> None:
        self.rest_api.query_order()

    def query_rest_data(self, event: Event) -> None:
        if not self.connected or not self.rest_api.time_synced:
            return
        self.query_count += 1
        if self.query_count < 6:
            return
        self.query_count = 0
        func = self.query_functions.pop(0)
        func()
        self.query_functions.append(func)

    def query_history(self, event: Event) -> list[BarData]:
        """兼容定时下载和 BaseGateway 的历史查询入口。"""
        if not self.history_contract or not self.rest_api.time_synced:
            return []
        symbol, exchange, _ = extract_vt_symbol(self.history_contract.pop(0))
        req = HistoryRequest(
            symbol=symbol,
            exchange=Exchange(exchange),
            interval=Interval.MINUTE,
            start=datetime.now(TZ_INFO) - timedelta(minutes=1440),
            end=datetime.now(TZ_INFO),
            #start=datetime(2026,8,5,tzinfo=TZ_INFO),
            #end=datetime(2026,10,27,tzinfo=TZ_INFO),
            gateway_name=self.gateway_name,
        )
        self.rest_api.query_history(req)

    def on_order(self, order: OrderData) -> None:
        """
        收到委托单推送，BaseGateway推送数据
        """
        self.orders[order.vt_orderid] = copy(order)
        super().on_order(order)

    def get_order(self, vt_orderid: str) -> OrderData | None:
        with self.order_lock:
            order = self.orders.get(vt_orderid)
            return copy(order) if order else None

    def get_active_orders(self, exchange: Exchange) -> list[OrderData]:
        with self.order_lock:
            return [
                copy(order) for order in self.orders.values()
                if order.exchange == exchange and order.status not in TERMINAL_STATUSES
            ]

    def close(self) -> None:
        self.connected = False
        self.event_engine.unregister(EVENT_TIMER, self.process_timer_event)
        self.event_engine.unregister(EVENT_TIMER, self.query_rest_data)
        self.event_engine.unregister(EVENT_TIMER, self.query_history)
        self.trade_ws_api.stop()
        self.market_ws_api.stop()
        self.rest_api.stop()

    def process_timer_event(self, event: Event) -> None:
        if not self.connected:
            return
        self.market_ws_api.flush_subscriptions()
        self.rest_api.keep_user_stream()
        if not self.rest_api.time_synced:
            return
        if self.rest_api.account_dirty and monotonic() >= self.rest_api.next_account_query:
            self.query_account()
        self.rest_api.repay_margin_debt()
        if self.leverage_contract:
            symbol, exchange, _ = extract_vt_symbol(self.leverage_contract.pop(0))
            if exchange in FUTURES_EXCHANGES:
                self.rest_api.set_leverage(symbol, exchange)


class BinanceOneRestApi(RestClient):
    """私有请求仅使用 PAPI，公共请求按路径分流且不携带API密钥。"""

    def __init__(self, gateway: BinanceOneGateway):
        super().__init__()
        self.gateway = gateway
        self.gateway_name = gateway.gateway_name
        self.trade_ws_api = gateway.trade_ws_api
        # 当前Rust客户端不会调用Python make_full_url覆盖；独立客户端才能正确分流。
        self.public_rest_apis = {exchange: RestClient() for exchange in PUBLIC_PATHS}
        self.key = ""
        self.secret = b""
        self.server = ""
        self.proxy_host = ""
        self.proxy_port = 0
        self.recv_window = 5000
        self.time_offset = 0
        self.time_synced = False
        self.last_time_query = 0.0
        self.user_stream_key = ""
        self.stream_pending = False
        self.next_stream_action = 0.0
        self.account_dirty = False
        self.next_account_query = 0.0
        self.account_date = None
        self.accounts_info: dict[str, dict] = {}
        self.balances: dict[str, dict] = {}
        self.balance_version = 0
        self.next_margin_repay = 0.0
        self.margin_repay_pending = False
        self.margin_repay_assets = ["USDT", "USDC"]
        self.spot_assets: dict[str, str] = {}
        self.contracts: dict[tuple[Exchange, str], ContractData] = {}
        self.position_symbols = {exchange: set() for exchange in FUTURES_EXCHANGES}
        self.position_versions: dict[tuple[Exchange, str], int] = {}
        self.position_modes: dict[Exchange, bool | None] = dict.fromkeys(FUTURES_EXCHANGES)
        self.order_count:int = 0
        self.state_lock = RLock()

    def stop(self) -> None:
        self.time_synced = False
        self.stream_pending = False
        self.user_stream_key = ""
        self.next_stream_action = 0
        self.margin_repay_pending = False
        self.next_margin_repay = 0.0
        super().stop()
        for api in self.public_rest_apis.values():
            api.stop()

    def get_timestamp(self) -> int:
        return int(time() * 1000) - self.time_offset

    def sign(self, request: Request) -> Request:
        security = (request.data or {}).get("security", Security.NONE)
        params = dict(request.params or {})
        request.data = None
        headers = dict(request.headers or {})
        if security == Security.NONE:
            headers.pop("X-MBX-APIKEY", None)
            request.headers = headers
            request.params = params
            return request
        headers.update({"X-MBX-APIKEY": self.key, "Accept": "application/json"})
        request.headers = headers
        if security == Security.SIGNED:
            params.update(timestamp=self.get_timestamp(), recvWindow=self.recv_window)
        params = {key: str(value).lower() if isinstance(value, bool) else value for key, value in params.items()}
        query = urlencode(sorted(params.items()))
        if security == Security.SIGNED:
            signature = hmac.new(self.secret, query.encode("utf-8"), hashlib.sha256).hexdigest()
            query += f"&signature={signature}"
        if query:
            request.path += "?" + query
        request.params = {}
        return request

    def connect(self, key: str, secret: str, server: str, proxy_host: str, proxy_port: int) -> None:
        if server != "REAL":
            raise ValueError("BINANCEONE仅支持统一账户实盘")
        self.key, self.secret = key, secret.encode("utf-8")
        self.server, self.proxy_host, self.proxy_port = server, proxy_host, proxy_port
        self.time_synced = False
        self.stream_pending = False
        self.user_stream_key = ""
        self.next_stream_action = 0
        self.margin_repay_pending = False
        self.next_margin_repay = 0.0
        self.margin_repay_assets = ["USDT", "USDC"]
        self.position_modes = dict.fromkeys(FUTURES_EXCHANGES)
        self.init(REST_HOST, proxy_host, proxy_port, gateway_name=self.gateway_name)
        self.start()
        for exchange, api in self.public_rest_apis.items():
            api.init(PUBLIC_REST_HOSTS[exchange], proxy_host, proxy_port, gateway_name=self.gateway_name)
            api.start()
        self.query_time()
        self.query_contract()
        self.gateway.write_log("BINANCEONE REST API启动，正在同步时间和查询三类市场合约")

    def query_time(self) -> Request:
        self.last_time_query = monotonic()
        return self.public_rest_apis[Exchange.BINANCE].add_request(
            "GET", "/api/v3/time", callback=self.on_query_time, extra=int(time() * 1000),
            on_failed=self.on_failed, on_error=self.on_error,
        )

    def on_query_time(self, data: dict, request: Request) -> None:
        self.time_offset = (int(request.extra) + int(time() * 1000)) // 2 - int(data["serverTime"])
        if self.time_synced or not self.gateway.connected:
            return
        self.time_synced = True
        self.next_margin_repay = monotonic() + 60
        for exchange in FUTURES_EXCHANGES:
            self.add_request(
                "GET", f"/papi/v1/{MARKET_NAMES[exchange]}/positionSide/dual",
                callback=self.on_query_position_mode, data={"security": Security.SIGNED}, extra=exchange,
            )
        self.query_account()
        self.query_position()
        self.query_order()
        self.start_user_stream()

    def on_query_position_mode(self, data: dict, request: Request) -> None:
        exchange = request.extra
        self.position_modes[exchange] = is_true(data["dualSidePosition"])
        if self.position_modes[exchange]:
            self.gateway.write_log(f"{exchange.value}处于双向持仓模式，禁止该市场下单；请先在币安切换为单向持仓")

    def query_contract(self) -> None:
        for exchange, path in PUBLIC_PATHS.items():
            self.public_rest_apis[exchange].add_request(
                "GET", path + "/exchangeInfo", callback=self.on_query_contract, extra=exchange,
                on_failed=self.on_failed, on_error=self.on_error,
            )

    def on_query_contract(self, data: dict, request: Request) -> None:
        exchange = request.extra
        for raw in data["symbols"]:
            if raw.get("contractStatus", raw.get("status")) != "TRADING":
                continue
            if exchange == Exchange.BINANCE:
                # 统一账户现货只能交易可全仓杠杆交易的币对。
                if not raw.get("isMarginTradingAllowed", False):
                    continue
            elif exchange == Exchange.BINANCES:
                if raw.get("contractType") != "PERPETUAL" or raw.get("quoteAsset") not in {"USDT", "USDC"}:
                    continue
            elif raw.get("contractType") != "PERPETUAL" and raw.get("deliveryDate", 0) <= int(time() * 1000):
                continue
            filters = {item["filterType"]: item for item in raw["filters"]}
            price_filter, lot_filter = filters.get("PRICE_FILTER", {}), filters.get("LOT_SIZE", {})
            contract = ContractData(
                symbol=raw["symbol"], name=raw["symbol"], exchange=exchange,
                product=Product.SPOT if exchange == Exchange.BINANCE else Product.FUTURES,
                size=float(raw["contractSize"]) if exchange == Exchange.BINANCEF else 1,
                price_tick=float(price_filter.get("tickSize", 0)),
                min_volume=float(lot_filter.get("minQty", 0)),
                max_volume=float(lot_filter.get("maxQty", 0)),
                min_price=float(price_filter.get("minPrice", 0)),
                max_price=float(price_filter.get("maxPrice", 0)), gateway_name=self.gateway_name,
            )
            contract.name = get_symbol_mark(contract.vt_symbol)
            contract.extra = {
                "base_asset": raw["baseAsset"], "quote_asset": raw["quoteAsset"],
                "margin_asset": raw.get("marginAsset", raw["quoteAsset"]),
                "min_qty": lot_filter.get("minQty", "0"), "filters": filters,
            }
            with self.state_lock:
                self.contracts[(exchange, contract.symbol)] = contract
                if exchange == Exchange.BINANCE:
                    self.spot_assets[contract.symbol] = raw["baseAsset"]
            self.gateway.on_contract(contract)
        if exchange == Exchange.BINANCE:
            self.push_spot_positions()
        self.gateway.write_log(f"BINANCEONE {exchange.value}合约信息查询成功")

    def repay_margin_debt(self) -> Request | None:
        """每60秒轮流全额偿还稳定币负债；每轮最多一次，避免耗尽6000/分钟权重。"""
        if not self.gateway.connected or not self.time_synced:
            return None
        now = monotonic()
        with self.state_lock:
            if self.margin_repay_pending or now < self.next_margin_repay:
                return None
            self.next_margin_repay = now + 60
            for _ in range(len(self.margin_repay_assets)):
                asset = self.margin_repay_assets.pop(0)
                self.margin_repay_assets.append(asset)
                raw = self.balances.get(asset, {})
                debt = Decimal(raw.get("crossMarginBorrowed") or "0") + Decimal(raw.get("crossMarginInterest") or "0")
                if debt > 0:
                    self.margin_repay_pending = True
                    break
            else:
                return None
        # 省略amount表示全额还款，仍受单次50000 USD上限及可用还款资产限制。
        return self.add_request(
            "POST", "/papi/v1/margin/repay-debt", callback=self.on_repay_margin_debt,
            params={"asset": asset}, data={"security": Security.SIGNED}, extra=asset,
            on_failed=self.on_repay_margin_debt_failed, on_error=self.on_repay_margin_debt_error,
        )

    def on_repay_margin_debt(self, data: dict, request: Request) -> None:
        self.margin_repay_pending = False
        self.account_dirty = True
        if is_true(data.get("success")):
            self.gateway.write_log(f"BINANCEONE {request.extra}杠杆还款成功，金额：{data.get('amount', '未知')}")
        else:
            self.gateway.write_log(f"BINANCEONE {request.extra}杠杆还款未成功：{data}")

    def on_repay_margin_debt_failed(self, status_code: int, request: Request) -> None:
        self.margin_repay_pending = False
        self.account_dirty = True
        self.gateway.write_log(f"BINANCEONE {request.extra}杠杆还款请求失败，将刷新账户并在后续轮次重新检查")
        self.on_failed(status_code, request)

    def on_repay_margin_debt_error(self, exception_type: type, exception_value: Exception, tb, request: Request) -> None:
        self.margin_repay_pending = False
        self.account_dirty = True
        self.gateway.write_log(f"BINANCEONE {request.extra}杠杆还款结果未知，将刷新账户并在后续轮次重新检查")
        self.on_error(exception_type, exception_value, tb, request)

    def query_account(self) -> None:
        if not self.time_synced:
            return
        self.account_dirty = False
        self.next_account_query = monotonic() + 5
        self.add_request(
            "GET", "/papi/v1/balance", callback=self.on_query_balance,
            data={"security": Security.SIGNED}, on_failed=self.on_account_failed, extra=self.balance_version,
        )
        self.add_request(
            "GET", "/papi/v1/account", callback=self.on_query_account,
            data={"security": Security.SIGNED}, on_failed=self.on_account_failed,
        )

    def on_query_balance(self, data: list | dict, request: Request) -> None:
        """
        各币种资产数量
        """
        rows = data if isinstance(data, list) else [data]
        with self.state_lock:
            if request.extra is not None and request.extra != self.balance_version:
                # 查询发起后已有钱包/负债推送，不用旧快照回滚现货仓位。
                self.account_dirty = True
                return
            self.balance_version += 1
            self.balances = {row["asset"]: dict(row) for row in rows}
            for row in rows:
                account = AccountData(
                    accountid=f"{row['asset']}_{self.gateway_name}",
                    balance=float(row.get("totalWalletBalance") or 0),
                    available=float(row.get("crossMarginFree") or 0),
                    frozen=float(row.get("crossMarginLocked") or 0),
                    position_profit=float(row.get("umUnrealizedPNL") or 0) + float(row.get("cmUnrealizedPNL") or 0),
                    datetime=datetime.now(TZ_INFO), file_name=self.gateway.account_file_name,
                    gateway_name=self.gateway_name,
                )
                account.extra = dict(row)
                # 包括清零资产，以便清除前一次账户缓存。
                self.gateway.on_account(account)
                self.accounts_info[account.accountid] = account.__dict__.copy()
        self.push_spot_positions()

    def on_query_account(self, data: dict, request: Request) -> None:
        """
        USD计价的统一账户资金
        """
        equity, margin = float(data["accountEquity"]), float(data["accountInitialMargin"])
        available = data.get("totalAvailableBalance")
        account = AccountData(
            accountid=f"USD_{self.gateway_name}", balance=equity, margin=margin,
            available=float(available) if available not in (None, "") else max(0, equity - margin),
            datetime=datetime.now(TZ_INFO), file_name=self.gateway.account_file_name, gateway_name=self.gateway_name,
        )
        account.extra = dict(data, available_estimated=available in (None, ""), account_scope="portfolio")
        self.gateway.on_account(account)
        with self.state_lock:
            self.accounts_info[account.accountid] = account.__dict__.copy()
        if data.get("accountStatus", "NORMAL") != "NORMAL":
            self.gateway.write_log(f"BINANCEONE统一账户风险状态：{data['accountStatus']}")
        self.save_account_snapshot()

    def save_account_snapshot(self) -> None:
        account_date = datetime.now(TZ_INFO).date()
        with self.state_lock:
            accounts = list(self.accounts_info.values())
        if not accounts:
            return
        path = Path(self.gateway.get_file_path.account_path(self.gateway.account_file_name))
        write_header = not path.exists()
        if not write_header and (self.account_date is None or self.account_date == account_date):
            self.account_date = account_date
            return
        try:
            with path.open("w" if write_header else "a", newline="", encoding="utf-8") as file:
                writer = csv.DictWriter(file, list(accounts[-1]))
                if write_header:
                    writer.writeheader()
                writer.writerows(accounts)
            self.account_date = account_date
        except OSError as exc:
            self.gateway.write_log(f"BINANCEONE账户快照写入失败：{exc}")

    def on_account_failed(self, status_code: int, request: Request) -> None:
        self.on_failed(status_code, request)
        try:
            data = request.response.json()
        except ValueError:
            return
        if data.get("code") == -2015:
            match = re.search(r"request ip:\s*([\da-fA-F:.]+)", data.get("msg", ""))
            ip = match.group(1) if match else "未知"
            error_monitor.send_text(f"BINANCEONE账户鉴权失败，请检查权限和IP白名单，当前请求IP：{ip}")
            error_monitor.last_text = ""

    def get_spot_symbols(self) -> set[str]:
        symbols = {
            req.symbol for req in list(self.gateway.market_ws_api.subscribed.values())
            if req.exchange == Exchange.BINANCE
        }
        for vt_symbol in self.gateway.recording_list:
            symbol, exchange, _ = extract_vt_symbol(vt_symbol)
            if exchange == Exchange.BINANCE:
                symbols.add(symbol)
        return symbols

    def push_spot_positions(self) -> None:
        for symbol in self.get_spot_symbols():
            self.push_spot_position(symbol)

    def push_spot_position(self, symbol: str) -> None:
        """现货持仓为全仓杠杆钱包基础币净资产，不包含合约抵押币。"""
        with self.state_lock:
            asset = self.spot_assets.get(symbol)
            if not asset or not self.balances:
                return
            raw = self.balances.get(asset, {})
            free = Decimal(raw.get("crossMarginFree") or "0")
            locked = Decimal(raw.get("crossMarginLocked") or "0")
            debt = Decimal(raw.get("crossMarginBorrowed") or "0") + Decimal(raw.get("crossMarginInterest") or "0")
            self.create_position_pair(symbol, Exchange.BINANCE, float(free + locked - debt), 0, 0, frozen=float(locked))

    def query_position(self) -> None:
        if not self.time_synced:
            return
        self.push_spot_positions()
        for exchange in FUTURES_EXCHANGES:
            with self.state_lock:
                versions = self.position_versions.copy()
            self.add_request(
                "GET", f"/papi/v1/{MARKET_NAMES[exchange]}/positionRisk", callback=self.on_query_position,
                data={"security": Security.SIGNED}, extra={"exchange": exchange, "versions": versions},
            )

    def on_query_position(self, data: list, request: Request) -> None:
        exchange = request.extra["exchange"]
        versions = request.extra["versions"]
        holding_symbols = {row["symbol"] for row in data}
        with self.state_lock:
            stale_symbols = {
                symbol for symbol in holding_symbols
                if self.position_versions.get((exchange, symbol), 0) != versions.get((exchange, symbol), 0)
            }
            hedge_symbols = {row["symbol"] for row in data if row.get("positionSide", "BOTH") != "BOTH"}

            for row in data:
                symbol = row["symbol"]
                if symbol in stale_symbols:
                    continue
                if symbol in hedge_symbols and row.get("positionSide", "BOTH") == "BOTH":
                    continue
                self.create_position_pair(
                    symbol, exchange, float(row["positionAmt"]), float(row["entryPrice"]),
                    float(row["unRealizedProfit"]), position_side=row.get("positionSide", "BOTH"),
                )
            # 只能清零本市场且查询发起后没有收到增量更新的持仓。
            watched = {
                req.symbol for req in list(self.gateway.market_ws_api.subscribed.values())
                if req.exchange == exchange
            }
            missing = self.position_symbols[exchange] | watched
            for symbol in missing - holding_symbols:
                key = (exchange, symbol)
                if self.position_versions.get(key, 0) == versions.get(key, 0):
                    self.create_position_pair(symbol, exchange, 0, 0, 0)
            self.position_symbols[exchange].update(holding_symbols)

    def create_position_pair(
        self, symbol: str, exchange: Exchange, volume: float, avg_price: float,
        unrealized_pnl: float, frozen: float = 0, position_side: str = "BOTH",
    ) -> None:
        with self.state_lock:
            key = (exchange, symbol)
            self.position_versions[key] = self.position_versions.get(key, 0) + 1
            if exchange in FUTURES_EXCHANGES:
                self.position_symbols[exchange].add(symbol)
            if position_side in {"LONG", "SHORT"}:
                # 双向账户只展示实际方向，不把另一个真实仓位清零，但仍禁止下单。
                self.position_modes[exchange] = True
                direction = Direction.LONG if position_side == "LONG" else Direction.SHORT
                directions = [direction]
            else:
                direction = Direction.LONG if volume >= 0 else Direction.SHORT
                directions = [Direction.LONG, Direction.SHORT]
            for side in directions:
                has_position = side == direction and volume != 0
                self.gateway.on_position(PositionData(
                    symbol=symbol, exchange=exchange, direction=side,
                    volume=abs(volume) if has_position else 0,
                    price=avg_price if has_position else 0, pnl=unrealized_pnl if has_position else 0,
                    frozen=min(abs(volume), frozen) if has_position else 0, gateway_name=self.gateway_name,
                ))

    def query_order(self) -> None:
        if not self.time_synced:
            return
        for exchange, market in MARKET_NAMES.items():
            active = self.gateway.get_active_orders(exchange)
            if exchange == Exchange.BINANCE:
                # margin/openOrders 无symbol会按全市场收取权重，轮询仅查跟踪币对。
                symbols = self.get_spot_symbols() | {order.symbol for order in active}
                for symbol in symbols:
                    self.add_request(
                        "GET", "/papi/v1/margin/openOrders", callback=self.on_query_order,
                        params={"symbol": symbol}, data={"security": Security.SIGNED},
                        extra={"exchange": exchange, "orders": [o for o in active if o.symbol == symbol]},
                    )
            else:
                self.add_request(
                    "GET", f"/papi/v1/{market}/openOrders", callback=self.on_query_order,
                    data={"security": Security.SIGNED}, extra={"exchange": exchange, "orders": active},
                )

    def on_query_order(self, data: list, request: Request) -> None:
        exchange = request.extra["exchange"]
        for raw in data:
            order = self.parse_order(raw, exchange)
            if order:
                self.gateway.on_order(order)

    def parse_order(self, raw: dict, exchange: Exchange, orderid: str = "") -> OrderData | None:
        order_type = get_order_type(raw["type"], raw["timeInForce"])
        status = STATUS_BINANCEONE2VT[raw["status"]]

        timestamp = raw.get("updateTime") or raw.get("time") or self.get_timestamp()
        order = OrderData(
            symbol=raw["symbol"], exchange=exchange,
            orderid=orderid or local_orderid(raw["symbol"], exchange, str(raw["clientOrderId"])),
            type=order_type, direction=DIRECTION_BINANCEONE2VT[raw["side"]],
            price=float(raw.get("price") or 0), volume=float(raw["origQty"]), traded=float(raw["executedQty"]),
            status=status, datetime=generate_datetime(timestamp), gateway_name=self.gateway_name,
        )
        if exchange != Exchange.BINANCE and is_true(raw.get("reduceOnly")):
            order.offset = Offset.CLOSE
        order.extra = {"update_time": int(timestamp), "binance_order_id": raw.get("orderId")}
        return order
    
    def _new_order_id(self) -> int:
        """
        返回加线程锁的order_count
        """
        with self.gateway.order_lock:
            self.order_count += 1
            return self.order_count
        
    def send_order(self, req: OrderRequest) -> str:
        self.count_datetime = int(datetime.now(TZ_INFO).strftime("%Y%m%d%H%M%S"))
        client_id = req.symbol + "-" + str(self.count_datetime) + str(self._new_order_id()).rjust(8,"0")
        order = req.create_order_data(local_orderid(req.symbol, req.exchange, client_id), self.gateway_name)
        self.gateway.on_order(order)

        order_type, time_condition = ORDERTYPE_VT2BINANCEONE[req.type]
        params = {
            "symbol": req.symbol, "side": DIRECTION_VT2BINANCEONE[req.direction], "type": order_type,
            "quantity": format_number(req.volume), "newClientOrderId": client_id, "newOrderRespType": "RESULT",
        }
        if time_condition:
            params.update(price=format_number(req.price), timeInForce=time_condition)
        if req.exchange == Exchange.BINANCE:
            # 只有开仓才允许自动借币
            if req.offset == Offset.OPEN:
                params["sideEffectType"] = "AUTO_BORROW_REPAY"
                params["autoRepayAtCancel"] = "true"
            else:
                params["sideEffectType"] = "AUTO_REPAY"
        else:
            params["positionSide"] = "BOTH"
            if req.offset in CLOSE_OFFSETS:
                params["reduceOnly"] = "true"
        self.add_request(
            "POST", f"/papi/v1/{MARKET_NAMES[req.exchange]}/order", callback=self.on_send_order,
            data={"security": Security.SIGNED}, params=params, extra=order,
            on_error=self.on_send_order_error, on_failed=self.on_send_order_failed,
        )
        return order.vt_orderid

    def on_send_order(self, data: dict, request: Request) -> None:
        return
        original = request.extra
        if "status" in data:
            order = self.parse_order(data, original.exchange, original.orderid)
            if order:
                self.gateway.on_order(order)
        else:
            # 兼容仅ACK响应；不能用旧的提交对象覆盖已经收到的成交。
            order = self.gateway.get_order(original.vt_orderid)
            if order and order.status == Status.SUBMITTING:
                order.status = Status.NOTTRADED
                self.gateway.on_order(order)

    def on_send_order_failed(self, status_code: int, request: Request) -> None:
        code = request.response.json()["code"]
        text = request.response.text
        order = self.gateway.get_order(request.extra.vt_orderid)
        if order:
            order.status = Status.REJECTED
            order.reject_code = str(code)
            self.gateway.on_order(order)
        self.gateway.write_log(f"BINANCEONE委托失败，HTTP {status_code}，信息：{text}")

    def on_send_order_error(self, exception_type: type, exception_value: Exception, trace_back, request: Request) -> None:
        """
        收到发送委托单错误回报
        """
        order = request.extra
        order.status = Status.REJECTED
        self.gateway.on_order(order)
        if not issubclass(exception_type, (ConnectionError, SSLError)):
            self.on_error(exception_type, exception_value, trace_back, request)

    def cancel_order(self, req: CancelRequest) -> Request | None:
        if req.exchange not in MARKET_NAMES or not self.time_synced:
            self.gateway.write_log("BINANCEONE撤单失败：市场不支持或时间同步未完成")
            return None
        return self.add_request(
            "DELETE", f"/papi/v1/{MARKET_NAMES[req.exchange]}/order", callback=self.on_cancel_order,
            params={"symbol": req.symbol, "origClientOrderId": client_orderid(req.symbol, req.exchange, req.orderid)},
            data={"security": Security.SIGNED}, extra=req, on_failed=self.on_cancel_failed,
        )

    def on_cancel_order(self, data: dict, request: Request) -> None:
        req = request.extra
        # 杠杆撤单响应clientOrderId是撤单请求ID，必须保留原委托ID。
        orderid = local_orderid(req.symbol, req.exchange, client_orderid(req.symbol, req.exchange, req.orderid))
        order = self.parse_order(data, req.exchange, orderid)
        if order:
            self.gateway.on_order(order)

    def on_cancel_failed(self, status_code: int, request: Request) -> None:
        # 撤单失败不是原订单被拒，不能改动原委托状态。
        self.on_failed(status_code, request)
        req = request.extra
        order = self.gateway.get_order(req.vt_orderid)
        if order:
            order.status = Status.REJECTED
            self.gateway.on_order(order)

    def set_leverage(self, symbol: str, exchange: Exchange) -> Request | None:
        if exchange not in FUTURES_EXCHANGES or not self.time_synced:
            return None
        return self.add_request(
            "POST", f"/papi/v1/{MARKET_NAMES[exchange]}/leverage", callback=self.on_leverage,
            data={"security": Security.SIGNED}, params={"symbol": symbol, "leverage": 10},
        )

    def on_leverage(self, data: dict, request: Request) -> None:
        pass

    def start_user_stream(self) -> Request | None:
        if self.stream_pending or not self.gateway.connected or not self.time_synced:
            return None
        self.stream_pending = True
        return self.add_request(
            "POST", "/papi/v1/listenKey", callback=self.on_start_user_stream, data={"security": Security.API_KEY},
            on_failed=self.on_stream_failed, on_error=self.on_stream_error,
        )

    def on_start_user_stream(self, data: dict, request: Request) -> None:
        self.stream_pending = False
        if not self.gateway.connected:
            return
        self.user_stream_key = data["listenKey"]
        self.next_stream_action = monotonic() + 30 * 60
        self.trade_ws_api.connect(WEBSOCKET_TRADE_HOST + self.user_stream_key, self.proxy_host, self.proxy_port)

    def keep_user_stream(self) -> None:
        now = monotonic()
        if now - self.last_time_query >= (300 if self.time_synced else 30):
            self.query_time()
        if not self.time_synced or self.stream_pending or now < self.next_stream_action:
            return
        if not self.user_stream_key:
            self.start_user_stream()
            return
        self.stream_pending = True
        self.add_request(
            "PUT", "/papi/v1/listenKey", callback=self.on_keep_user_stream, data={"security": Security.API_KEY},
            on_failed=self.on_stream_failed, on_error=self.on_stream_error,
        )

    def on_keep_user_stream(self, data: dict, request: Request) -> None:
        self.stream_pending = False
        self.next_stream_action = monotonic() + 30 * 60

    def on_stream_failed(self, status_code: int, request: Request) -> None:
        self.stream_pending = False
        self.next_stream_action = monotonic() + 30
        try:
            code = request.response.json().get("code")
        except ValueError:
            code = None
        if code == -1125:
            self.user_stream_key = ""
            self.start_user_stream()
        self.on_failed(status_code, request)

    def on_stream_error(self, exception_type: type, exception_value: Exception, tb, request: Request) -> None:
        self.stream_pending = False
        self.next_stream_action = monotonic() + 30
        self.on_error(exception_type, exception_value, tb, request)

    def on_failed(self, status_code: int, request: Request) -> None:
        # 基础客户端会输出完整签名和API key；本网关仅输出无查询串的路径。
        path = request.path.split("?", 1)[0]
        text = request.response.text if request.response is not None else "无响应"
        self.gateway.write_log(f"BINANCEONE REST请求失败：{request.method} {path}，HTTP {status_code}，{text}")

    def on_error(self, exception_type: type, exception_value: Exception, tb, request: Request | None) -> None:
        path = request.path.split("?", 1)[0] if request else "未知路径"
        self.gateway.write_log(f"BINANCEONE REST异常：{path}，{exception_type.__name__}")

    def query_history(self, req: HistoryRequest) -> list[BarData]:

        history = []
        limit = 200
        start_time = req.start
        end = req.end or datetime.now(TZ_INFO)
        interval = TIMEDELTA_MAP[req.interval]
        started = monotonic()
        while start_time <= end:
            end_time = min(start_time + interval * limit - timedelta(milliseconds=1), end)
            response = self.public_rest_apis[req.exchange].request(
                "GET", PUBLIC_PATHS[req.exchange] + "/klines",
                params={
                    "symbol": req.symbol, "interval": INTERVAL_VT2BINANCEONE[req.interval], "limit": limit,
                    "startTime": int(start_time.timestamp() * 1000), "endTime": int(end_time.timestamp() * 1000),
                },
            )
            if response is None or response.status_code // 100 != 2:
                self.gateway.write_log(f"{req.vt_symbol}历史查询失败，HTTP {getattr(response, 'status_code', '无响应')}")
                break
            data = response.json()
            if not data:
                start_time = end_time + timedelta(milliseconds=1)
                continue
            for raw in data:
                dt = generate_datetime(raw[0])
                if req.start <= dt <= end:
                    history.append(BarData(
                        symbol=req.symbol, exchange=req.exchange, datetime=dt, interval=req.interval,
                        volume=float(raw[7] if req.exchange == Exchange.BINANCEF else raw[5]),  # BINANCE，BINANCEF为币的成交量，
                        open_price=float(raw[1]), high_price=float(raw[2]), low_price=float(raw[3]),
                        close_price=float(raw[4]), gateway_name=self.gateway_name,
                    ))
            next_start = generate_datetime(data[-1][0]) + interval
            if next_start <= start_time:
                self.gateway.write_log(f"{req.vt_symbol}历史分页未前进，停止查询")
                break
            start_time = next_start
        if history:
            from vnpy.trader.database import database_manager
            try:
                database_manager.save_bar_data(history, False)
                self.gateway.write_log(f"载入{req.vt_symbol}历史数据{len(history)}条，耗时{monotonic() - started:.3f}秒")
            except Exception as exc:
                self.gateway.write_log(f"{req.vt_symbol}历史数据保存失败：{exc}")


class BinanceOneTradeWebsocketApi(WebsocketClient):
    """同一条 PM 私有连接接收 margin、UM、CM 三个业务分区。"""

    def __init__(self, gateway: BinanceOneGateway):
        super().__init__()
        self.gateway = gateway
        self.gateway_name = gateway.gateway_name

    def connect(self, url: str, proxy_host: str, proxy_port: int) -> None:
        self.init(url, proxy_host, proxy_port, gateway_name=self.gateway_name)
        if self._active:
            # 更新过期listenKey时复用现有工作线程，不重复启动心跳线程。
            self._disconnect()
        else:
            self.start()

    def on_connected(self) -> None:
        self.gateway.write_log("BINANCEONE统一账户Websocket交易连接成功")

    def on_disconnected(self) -> None:
        self.gateway.write_log("BINANCEONE统一账户Websocket交易连接断开")

    def on_packet(self, packet: dict) -> None:
        if not isinstance(packet, dict):
            return
        packet = packet.get("data", packet)
        event = packet.get("e")
        rest = self.gateway.rest_api
        if event == "ACCOUNT_UPDATE":
            self.on_position(packet)
            rest.account_dirty = True
        elif event == "ORDER_TRADE_UPDATE":
            self.on_order(packet)
        elif event == "executionReport":
            self.on_execution_report(packet)
        elif event == "outboundAccountPosition":
            with rest.state_lock:
                rest.balance_version += 1
                for raw in packet.get("B", []):
                    asset = rest.balances.setdefault(raw["a"], {"asset": raw["a"]})
                    asset.update(crossMarginFree=raw["f"], crossMarginLocked=raw["l"])
            rest.push_spot_positions()
            rest.account_dirty = True
        elif event == "liabilityChange":
            with rest.state_lock:
                rest.balance_version += 1
                asset = rest.balances.setdefault(packet["a"], {"asset": packet["a"]})
                asset.update(crossMarginBorrowed=packet["p"], crossMarginInterest=packet["i"])
            rest.push_spot_positions()
            rest.account_dirty = True
        elif event in {"balanceUpdate", "openOrderLoss"}:
            rest.account_dirty = True
        elif event == "listenKeyExpired":
            rest.user_stream_key = ""
            rest.stream_pending = False
            rest.start_user_stream()
        elif event in {"RISK_LEVEL_CHANGE", "riskLevelChange"}:
            self.gateway.write_log(f"BINANCEONE账户风险通知：{packet}")
        elif event and event not in {"ACCOUNT_CONFIG_UPDATE", "CONDITIONAL_ORDER_TRADE_UPDATE", "ALGO_UPDATE"}:
            self.gateway.write_log(f"BINANCEONE未处理的私有事件类型：{event}")

    def on_position(self, packet: dict) -> None:
        exchange = BUSINESS_EXCHANGES.get(packet.get("fs"))
        for raw in packet.get("a", {}).get("P", []):
            self.gateway.rest_api.create_position_pair(
                raw["s"], exchange, float(raw["pa"]), float(raw["ep"]),
                float(raw.get("up", 0)), position_side=raw.get("ps", "BOTH"),
            )

    def on_order(self, packet: dict) -> None:
        exchange = BUSINESS_EXCHANGES.get(packet.get("fs"))
        if exchange is None:
            self.gateway.write_log("BINANCEONE订单推送缺少有效业务分区，已忽略")
            return
        self.process_order(packet["o"], exchange, int(packet["E"]))

    def on_execution_report(self, packet: dict) -> None:
        raw = dict(packet)
        # 现货撤单推送的c是撤单请求ID，C才是被撤委托的客户端编号。
        if raw.get("x") == "CANCELED" and raw.get("C"):
            raw["c"] = raw["C"]
        self.process_order(raw, Exchange.BINANCE, int(packet["E"]))
        self.gateway.rest_api.account_dirty = True

    def process_order(self, raw: dict, exchange: Exchange, timestamp: int) -> None:
        order_type = get_order_type(raw["o"], raw["f"])
        status = STATUS_BINANCEONE2VT[raw["X"]]

        order = OrderData(
            symbol=raw["s"], exchange=exchange, orderid=local_orderid(raw["s"], exchange, str(raw["c"])),
            type=order_type, direction=DIRECTION_BINANCEONE2VT[raw["S"]],
            price=float(raw["p"]), volume=float(raw["q"]), traded=float(raw["z"]), status=status,
            datetime=generate_datetime(timestamp), gateway_name=self.gateway_name,
        )

        order.extra = {"update_time": timestamp, "binance_order_id": raw.get("i")}
        if exchange != Exchange.BINANCE and is_true(raw.get("R")):
            order.offset = Offset.CLOSE
        self.gateway.on_order(order)
        volume = float(raw.get("l", 0))
        if raw.get("x") != "TRADE" or not volume or int(raw.get("t", -1)) < 0:
            return
        # 成交ID跨市场/币对并不唯一，同时防止重连重复回报导致重复记账。
        tradeid = f"{MARKET_NAMES[exchange]}:{order.symbol}:{raw['t']}"

        latest = self.gateway.get_order(order.vt_orderid)
        trade = TradeData(
            symbol=order.symbol, exchange=exchange, orderid=order.orderid, tradeid=tradeid,
            direction=order.direction, offset=latest.offset if latest else order.offset,
            price=float(raw["L"]), volume=volume, datetime=generate_datetime(raw.get("T", timestamp)),
            gateway_name=self.gateway_name,
        )
        trade.extra = {"commission": float(raw.get("n") or 0), "commission_asset": raw.get("N")}
        self.gateway.on_trade(trade)


class BinanceOneDataWebsocketApi:
    """行情聚合层；缓存使用完整vt_symbol，现货和永续同名币对不冲突。"""

    def __init__(self, gateway: BinanceOneGateway):
        self.gateway = gateway
        self.gateway_name = gateway.gateway_name
        self.ticks: dict[str, TickData] = {}
        self.subscribed: dict[str, SubscribeRequest] = {}
        self.tick_lock = Lock()
        self.connections = {
            key: BinanceOneMarketWebsocketApi(self, *key) for key in DATA_HOSTS
        }

    def connect(self, proxy_host: str, proxy_port: int, server: str) -> None:
        if server != "REAL":
            raise ValueError("BINANCEONE行情仅支持实盘市场")
        if self.gateway.publish_status:
            for api in self.connections.values():
                api.connect(proxy_host, proxy_port)

    def stop(self) -> None:
        for api in self.connections.values():
            api.stop()

    def subscribe(self, req: SubscribeRequest) -> None:
        if req.exchange not in MARKET_NAMES:
            self.gateway.write_log(f"BINANCEONE行情不支持该市场：{req.exchange.value}")
            return
        with self.tick_lock:
            self.subscribed[req.vt_symbol] = req
            if req.vt_symbol not in self.ticks:
                self.ticks[req.vt_symbol] = TickData(
                    symbol=req.symbol, exchange=req.exchange, name=get_symbol_mark(req.vt_symbol),
                    datetime=datetime.now(TZ_INFO), gateway_name=self.gateway_name,
                )
        if self.gateway.publish_status:
            for (exchange, _), api in self.connections.items():
                if exchange == req.exchange:
                    api.subscribe(req)

    def flush_subscriptions(self) -> None:
        for api in self.connections.values():
            api.flush_subscriptions()

    def on_data(self, exchange: Exchange, symbol: str, channel: str, data: dict) -> None:
        vt_symbol = f"{symbol}_{exchange.value}/{self.gateway_name}"
        with self.tick_lock:
            tick = self.ticks.get(vt_symbol)
            if tick is None:
                return
            timestamp = data.get("T",data.get("E",self.gateway.rest_api.get_timestamp()))     #T 成交时间，E事件时间，首选T，T缺失再选E
            tick.datetime = generate_datetime(timestamp) if timestamp else datetime.now(TZ_INFO)
            if channel == "miniTicker":
                # CM的v是张数、q是基础币数量；现货和UM的v才是基础币数量。
                tick.volume = float(data["q"] if exchange == Exchange.BINANCEF else data["v"])
                tick.open_price, tick.high_price = float(data["o"]), float(data["h"])
                tick.low_price, tick.last_price = float(data["l"]), float(data["c"])
            elif channel.startswith("depth"):
                bids, asks = data.get("b",data["bids"]), data.get("a",data["asks"])
                for side, levels in (("bid", bids), ("ask", asks)):
                    for index in range(5):
                        price, volume = levels[index]
                        setattr(tick, f"{side}_price_{index + 1}", float(price))
                        setattr(tick, f"{side}_volume_{index + 1}", float(volume))
            elif channel == "bookTicker":
                tick.bid_price_1, tick.bid_volume_1 = float(data["b"]), float(data["B"])
                tick.ask_price_1, tick.ask_volume_1 = float(data["a"]), float(data["A"])
            elif channel in {"trade", "aggTrade"}:
                tick.last_price, tick.last_volume = float(data["p"]), float(data["q"])
            else:
                return
            if tick.last_price:
                self.gateway.on_tick(copy(tick))


class BinanceOneMarketWebsocketApi(WebsocketClient):
    """单个公共行情连接；订阅先缓存，再限速批量发送，不阻塞调用者。"""

    def __init__(self, api: BinanceOneDataWebsocketApi, exchange: Exchange, category: str):
        super().__init__()
        self.api, self.gateway = api, api.gateway
        self.gateway_name = api.gateway_name
        self.exchange, self.category = exchange, category
        self.connection_status = False
        self.reqid = 0
        self.pending: dict[str, SubscribeRequest] = {}
        self.sent: set[str] = set()
        self.subscription_lock = RLock()
        self.next_subscribe = 0.0

    def connect(self, proxy_host: str, proxy_port: int) -> None:
        self.init(DATA_HOSTS[(self.exchange, self.category)], proxy_host, proxy_port, gateway_name=self.gateway_name)
        if not self._active:
            self.start()

    def on_connected(self) -> None:
        with self.subscription_lock:
            self.connection_status = True
            self.sent.clear()
            self.next_subscribe = 0
            for req in list(self.api.subscribed.values()):
                if req.exchange == self.exchange:
                    self.pending[req.vt_symbol] = req
        self.gateway.write_log(f"BINANCEONE {self.exchange.value}/{self.category}行情连接成功")
        self.flush_subscriptions()

    def on_disconnected(self) -> None:
        self.connection_status = False
        self.gateway.write_log(f"BINANCEONE {self.exchange.value}/{self.category}行情连接断开")

    def subscribe(self, req: SubscribeRequest) -> None:

        with self.subscription_lock:
            if req.vt_symbol not in self.sent:
                self.pending[req.vt_symbol] = req
        self.flush_subscriptions()

    def get_subscribe_params(self, req: SubscribeRequest) -> list[str]:
        symbol = req.symbol.lower()
        params = []
        if self.category != "market":
            params.append(symbol + "@depth5@100ms")
            # 逐笔一档深度
            #params.append(symbol + "@bookTicker")
        if self.category != "public":
            params.append(symbol + "@miniTicker")
            if self.gateway.book_trade_status:
                params.append(symbol + ("@trade" if self.exchange == Exchange.BINANCE else "@aggTrade"))
        return params

    def flush_subscriptions(self) -> None:
        with self.subscription_lock:
            if not self.connection_status or monotonic() < self.next_subscribe or not self.pending:
                return
            reqs = list(self.pending.values())[:50]
            params = [stream for req in reqs for stream in self.get_subscribe_params(req)]
            self.reqid += 1
            self.send_packet({"method": "SUBSCRIBE", "params": params, "id": self.reqid})
            for req in reqs:
                self.pending.pop(req.vt_symbol, None)
                self.sent.add(req.vt_symbol)
            self.next_subscribe = monotonic() + 0.25

    def on_packet(self, packet: dict) -> None:
        if not isinstance(packet, dict):
            return
        if "code" in packet:
            self.gateway.write_log(f"BINANCEONE {self.exchange.value}行情订阅失败：{packet}")
            return
        stream = packet.get("stream", "")
        data = packet.get("data", packet)
        if stream:
            symbol, channel = stream.split("@", 2)[:2]
            symbol = symbol.upper()
        else:
            symbol = data.get("s")
            channel = {"24hrMiniTicker": "miniTicker", "depthUpdate": "depth5"}.get(data.get("e"), "")

        if symbol:
            self.api.on_data(self.exchange, symbol, channel, data)

