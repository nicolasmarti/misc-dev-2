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
c.m_exchange = "NYSE"
c.m_currency = "USD"

order = Order()
order.m_action = "BUY"
order.m_tif = "DAY"
order.m_orderType = 'LMT'
order.m_totalQuantity = 100
order.m_openClose = "O"
order.m_lmtPrice = float(round(120,2))

#print "orderId1: " + str(o.placeOrder(c, order, None))

print "orderId1: " + str(o.placeOrder(c, order, timedelta(seconds=3)))

sleep(30)

o.exit()
