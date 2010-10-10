import Pyro.core

from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription
from ib.ext.ExecutionFilter import ExecutionFilter

from time import *
from datetime import *

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

f = ExecutionFilter()

print str(o.reqExecutions(f))

