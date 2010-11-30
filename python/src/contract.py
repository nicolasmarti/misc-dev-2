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


    def __del__(self):
        
        self.con.cancelMktData(self.mktDataId)
        self.con.cancelMktData(self.cancelMktDepth)

    def __str__(self):        
        return "Contract"

    def __getattr__(self, name):
        if name == "mktdata":
            return self.con.getMktData(self.mktDataId)
        elif name == "mkdepth":
            return self.con.getMktDepth(self.cancelMktDepth)

        return None

    def __getitem__(self, key):
        if key == "mktdata":
            return self.con.getMktData(self.mktDataId)
        elif key == "mkdepth":
            return self.con.getMktDepth(self.cancelMktDepth)


    def getNextId(self):
        self.m_lock.acquire()
        res = self.m_nextid
        self.m_nextid += 1
        self.m_lock.release()
        return res
