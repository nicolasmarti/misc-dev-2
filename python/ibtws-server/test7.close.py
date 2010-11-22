import Pyro.core
import time

from Pyro.EventService.Clients import Subscriber

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

o.cancelNewsBulletins()
