# Imports

# for thread lock
from threading import *

# for time-related functions
from time import *
from datetime import *

# general
import sys
import os

# for ib
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription
from ib.ext.ExecutionFilter import ExecutionFilter

# for pyro
import Pyro.core
import Pyro.naming
import Pyro.constants
import Pyro.EventService.Clients



# TODO: implement a + * / --> allow to build a portfolio (can be seen as a stock)

class Stock:

    def __init__(self, name):
        
        self.m_lock = Lock()
        
        self.m_nextid = 0
        
        c = Contract()
        c.m_symbol = name
        c.m_secType = "STK"

        self.con = Pyro.core.getProxyForURI("PYRONAME://serverInterface")
        self.contract = self.con.reqContractDetails(c)[0].m_summary
        
        self.mktDataId = self.con.reqMktData(self.contract, False)
        self.mktDepthId = self.con.reqMktDepth(self.contract, 10)
        self.mktRTBarId = self.con.reqRTData(self.contract, 5, "MIDPOINT", 0)


        self.oids = []

    def __del__(self):
        
        self.con.cancelMktData(self.mktDataId)
        self.con.cancelMktDepth(self.MktDepthId)
        self.con.cancelRTData(self.mktRTBarId)

    def __str__(self):        
        return "Contract"

    def __getattr__(self, name):
        if name == "order":
            def order(position = "BUY", orderty = "MKT", quantity = 100, price = None, timeout = None, openClose = "O"):
                order = Order()
                order.m_action = position
                order.m_tif = "DAY"
                order.m_orderType = orderty
                order.m_totalQuantity = quantity
                order.m_openClose = openClose
                if price <> None: order.m_lmtPrice = price

                if position == "BUY":
                    pos = quantity
                else:
                    pos = -quantity

                if price == None and orderty <> "MKT": order.m_lmtPrice = self.best_price(pos)
                
                if timeout == None:
                    oid = self.con.placeOrder(self.contract, order, None)
                    self.oids.append(oid)
                    return oid
                else:
                    oid = self.con.placeOrder(self.contract, order, timedelta(seconds=timeout))
                    if oid == None:
                        return None
                    else:
                        self.oids.append(oid)
                        return oid
            return order
        elif name == "close":
            def close(orderty = "MKT", price = None, timeout = None):
                position = self["position"]
                order = Order()
                if position > 0:
                    order.m_action = "SELL"
                else:
                    order.m_action = "BUY"
                order.m_tif = "DAY"
                order.m_orderType = orderty
                order.m_totalQuantity = abs(position)
                order.m_openClose = "C"
                if price <> None: order.m_lmtPrice = price

                if price == None and orderty <> "MKT": order.m_lmtPrice = self.best_price(position)
                
                if timeout == None:
                    oid = self.con.placeOrder(self.contract, order, None)
                    self.oids.append(oid)
                    return oid
                else:
                    oid = self.con.placeOrder(self.contract, order, timedelta(seconds=timeout))
                    if oid == None:
                        return None
                    else:
                        self.oids.append(oid)
                        return oid
            return close
        elif name == "best_price":
            # determine the best price to ask/bid for a given position, depending on the mkt depth
            def best_price(position):
                #return self.con.getMktData(self.mktDataId)["LAST PRICE"]
                mktdepth = self.con.getMktDepth(self.mktDepthId)
                if position > 0:
                    if (mktdepth[0][0]) <> None: return mktdepth[0][0][0]
                else:
                    if (mktdepth[1][0]) <> None: return mktdepth[1][0][0]
                return self["mktdata"]["LAST PRICE"]
            return best_price
        elif name == "cancel":
            def cancel():
                for i in self.oids:
                    if self.con.orderStatus(i)[1][1] == "PendingSubmit" or self.con.orderStatus(i)[1][1] == "PreSubmitted" or self.con.orderStatus(i)[1][1] == "Submitted":
                        self.con.cancelOrder(i)
            return cancel
        else:
            return None

    def __getitem__(self, key):
        if key == "mktdata":
            return self.con.getMktData(self.mktDataId)
        elif key == "mktdepth":
            return self.con.getMktDepth(self.mktDepthId)
        elif key == "orders":
            l = []
            for i in self.oids:
                l.append(self.con.orderStatus(i))
            return l
        elif key == "rtbar":
            return self.con.getRTData(self.mktRTBarId)
        elif key == "ordervalue":
            def ordervalue(i):
                if len(self.con.orderStatus(i)[1]) > 2:
                    if self.con.orderStatus(i)[0][1].m_action == "BUY": 
                        mul = -1
                    else:
                        mul = 1
                    filled = self.con.orderStatus(i)[1][2]
                    avgPrice = self.con.orderStatus(i)[1][4]
                    return mul * filled * avgPrice            
                sleep(1)
                return ordervalue(i)
            return ordervalue
        elif key == "pnl" or key == "upnl" or key == "position" or key == "value":
            pnl = 0.0
            upnl = [0, 0.0]
            for i in self.oids:
                if len(self.con.orderStatus(i)[1]) > 2:
                    if self.con.orderStatus(i)[0][1].m_action == "BUY": 
                        mul = -1
                    else:
                        mul = 1
                    filled = self.con.orderStatus(i)[1][2]
                    avgPrice = self.con.orderStatus(i)[1][4]

                    # case analysis: 
                    if mul >= 0 and upnl[0] >= 0:
                        # here we SELL and or upnl is long
                        if filled > upnl[0]:
                            # we sold more than we own
                            pnl += upnl[0] * (avgPrice - upnl[1])
                            upnl[0] = upnl[0] - filled
                            upnl[1] = avgPrice
                        elif filled < upnl[0]:
                            # we sold less than we own
                            pnl += filled * (avgPrice - upnl[1])
                            upnl[0] = upnl[0] - filled
                        elif filled == upnl[0]:
                            pnl += filled * (avgPrice - upnl[1])
                            upnl[0] = 0
                    elif mul <= 0 and upnl <= 0:
                        # here we BUY and or upnl is short
                        if filled > -upnl[0]:
                            # we buy more than we are short
                            pnl += -upnl[0] * (upnl[1] - avgPrice)
                            upnl[0] = filled + upnl[0]
                            upnl[1] = avgPrice
                        elif filled < -upnl[0]:
                            # we buy less then we are short
                            pnl += filled * (upnl[1] - avgPrice)
                            upnl[0] = filled + upnl[0]
                        elif filled == upnl[0]:
                            pnl += -filled * (upnl[1] - avgPrice)
                            upnl[0] = 0
                    elif mul <= 0 and upnl[0] >= 0:
                        # we buy stock and are already long
                        if (filled + upnl[0]) == 0:
                            upnl[1] = 0.0
                        else:
                            upnl[1] = (filled * avgPrice + upnl[0] * upnl[1]) / (filled + upnl[0])
                        upnl[0] = filled + upnl[0]
                    elif mul >= 0 and upnl[0] <= 0:
                        # we sell stock and are already short
                        if (filled - upnl[0]) == 0:
                            upnl[1] = 0.0
                        else:
                            upnl[1] = (filled * avgPrice + -upnl[0] * upnl[1]) / (filled - upnl[0])
                        upnl[0] = -filled + upnl[0]

            if key == "position": return upnl[0]
            if key == "pnl": return pnl
            if key == "upnl": 
                if upnl[0] < 0:
                    return - upnl[0] * (upnl[1] - self.con.getMktData(self.mktDataId)["ASK PRICE"])
                else:
                    return upnl[0] * (self.con.getMktData(self.mktDataId)["BID PRICE"] - upnl[1])
            if key == "value":
                upnl[0] * upnl[1]
                


