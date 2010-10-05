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
c.m_exchange = "NYSE"
c.m_currency = "USD"

dataid = o.reqMktData(c, False)

print dataid

print str(o.getData(dataid))

sleep(1)

print str(o.getData(dataid))

sleep(1)

print str(o.getData(dataid))

sleep(1)

print str(o.getData(dataid))

sleep(1)

print str(o.getData(dataid))

sleep(1)

o.cancelMktData(dataid)
