import Pyro.core
import time

from Pyro.EventService.Clients import Subscriber

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

o.setCell(0,0, (0,0), "=1+A2")
o.setCell(0,0, (0,1), "=1+8")

