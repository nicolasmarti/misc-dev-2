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
subscript.m_locationCode = 'STK.AMEX'
subscript.m_scanCode = "MOST_ACTIVE"
subscript.m_stockTypeFilter = 'ALL' 
subscript.m_m_abovePrice = 0.0
subscript.m_aboveVolume = 0
subscript.m_marketCapAbove = 0.0

#o.scanParam()

print str(o.scanMkt(subscript))
