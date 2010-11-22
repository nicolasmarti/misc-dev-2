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

dataid = o.reqFundamentalData(c, "Summary")

print dataid

sleep(10)

print o.getFundamentalData(dataid)

o.cancelFundamentalData(dataid)
