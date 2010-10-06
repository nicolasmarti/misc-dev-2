import Pyro.core

from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

from Pyro.EventService.Clients import Subscriber

from time import *
from datetime import *

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")



c = Contract()
c.m_symbol = "GS"
c.m_secType = 'STK'
c.m_exchange = "SMART"
c.m_currency = "USD"

order1 = Order()
order1.m_action = "BUY"
order1.m_tif = "DAY"
order1.m_orderType = 'LMT'
order1.m_totalQuantity = 100
order1.m_openClose = "O"
order1.m_lmtPrice = float(round(120,2))

order2 = Order()
order2.m_action = "BUY"
order2.m_tif = "DAY"
order2.m_orderType = 'LMT'
order2.m_totalQuantity = 100
order2.m_openClose = "O"
order2.m_lmtPrice = float(round(130,2))

oid1 = o.placeOrder(c, order2, None)
print "orderId1: " + str(oid1)

oid2 = o.placeOrder(c, order1, timedelta(seconds=3))
print "orderId2: " + str(oid2)

sleep(10)

print o.orderStatus(oid1)
print o.orderStatus(oid2)

#o.cancelOrder(oid1)

print 

#o.exit()
