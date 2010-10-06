import Pyro.core

from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

from time import *
from datetime import *

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

c = Contract()
c.m_symbol = "GS"
c.m_secType = 'STK'
c.m_exchange = "SMART"
c.m_currency = "USD"

dataid = o.reqMktDepth(c, 10)

print dataid

print str(o.getMktDepth(dataid))

sleep(1)

print str(o.getMktDepth(dataid))

sleep(1)

print str(o.getMktDepth(dataid))

sleep(1)

print str(o.getMktDepth(dataid))

sleep(1)

print str(o.getMktDepth(dataid))

sleep(1)

o.cancelMktDepth(dataid)
