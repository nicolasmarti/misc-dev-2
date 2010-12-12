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

        self.oids = []

    def __del__(self):
        
        self.con.cancelMktData(self.mktDataId)
        self.con.cancelMktData(self.cancelMktDepth)

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
                if price <> None: order.m_lmtPrice = float(round(float(price)))

                if position == "BUY":
                    pos = quantity
                else:
                    pos = -quantity

                if price == None and orderty <> "MKT": order.m_lmtPrice = float(round(float(self.best_price(pos))))
                
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
                if price <> None: order.m_lmtPrice = float(round(float(price)))

                if price == None and orderty <> "MKT": order.m_lmtPrice = float(round(float(self.best_price(position))))
                
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
        elif key == "position":
            position = 0
            for i in self.oids:
                if len(self.con.orderStatus(i)[1]) > 2:
                    if self.con.orderStatus(i)[0][1].m_action == "BUY": 
                        mul = 1
                    else:
                        mul = -1
                    position += mul * self.con.orderStatus(i)[1][2]
            return position
    
        # determine the best price to ask/bid for a given position, depending on the mkt depth
        def best_price(self, position):
            mktdepth = self.con.getMktDepth(self.mktDepthId)
            if position > 0:
                if (mktdepth[0][0][0]) <> None: return mktdepth[0][0][0]
            else:
                if (mktdepth[1][0][0]) <> None: return mktdepth[1][0][0]
            return 0

