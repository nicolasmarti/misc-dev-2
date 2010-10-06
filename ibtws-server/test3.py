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
subscript.m_scanCode = 'TOP_PERC_GAIN' 
subscript.m_instrument = 'STK' 
subscript.m_abovePrice = ''
subscript.m_belowPrice = ''
subscript.m_stockTypeFilter = 'ALL' 
subscript.locationCode('STK.NASDAQ.NMS') 
subscript.m_averageOptionVolumeAbove = '' 
subscript.m_couponRateAbove = '' 
subscript.m_couponRateBelow = '' 
subscript.m_marketCapAbove = '' 
subscript.m_marketCapBelow = '' 
subscript.m_aboveVolume = '' 

#o.scanParam()

print str(o.scanMkt(subscript))
