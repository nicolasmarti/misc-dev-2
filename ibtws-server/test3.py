import Pyro.core

from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

from Pyro.EventService.Clients import Subscriber

from time import *
from datetime import *

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

subscript = ScannerSubscription() 
subscript.numberOfRows(200) 
subscript.m_instrument = 'STK' 
subscript.m_locationCode('STK.US') 
subscript.m_scanCode("MOST_ACTIVE")
subscript.m_stockTypeFilter = 'ALL' 

#o.scanParam()

print str(o.scanMkt(subscript))
