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

mnow = datetime.now()

delta = timedelta(hours=2)

mstr = (mnow - delta).strftime("%Y%m%d %H:%M:%S")

print mstr

dataid = o.reqHistData(c, mstr, "1000", "5 mins", "MIDPOINT", 0, 1)

print dataid

sleep(10)

print o.getHistData(dataid)

o.cancelHistData(dataid)
