import Pyro.core

from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

from time import *
from datetime import *

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

c = Contract()
c.m_symbol = "DELL"
c.m_secType = 'STK'
c.m_exchange = "SMART"
c.m_currency = "USD"

dataid = o.reqHistData(c, "20101008 22:00:00", "1000", "5 mins", "MIDPOINT", 0, 1)

print dataid

sleep(10)

print o.getHistData(dataid)

o.cancelHistData(dataid)
