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
#c.m_exchange = "SMART"
c.m_currency = "USD"

l = o.reqContractDetails(c)

for i in l:
    print "MarketName: " + i.m_marketName + ", secType:" + i.m_summary.m_secType + ", exchange: " + i.m_summary.m_exchange

#c2 = Contract()
#c2.m_symbol = "GS"
#c2.m_secType = 'OPT'
#c2.m_exchange = "SMART"
#c2.m_currency = "USD"

#print str(len(o.reqContractDetails(c2)))
