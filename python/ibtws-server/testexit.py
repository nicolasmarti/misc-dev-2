import Pyro.core

from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

from Pyro.EventService.Clients import Subscriber

from time import *
from datetime import *

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

try:
    o.exit()
except:
    pass
