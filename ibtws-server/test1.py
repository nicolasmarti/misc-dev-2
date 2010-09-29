import Pyro.core
import time

from Pyro.EventService.Clients import Subscriber

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

class StockSubscriber(Subscriber):
    def __init__(self):
        Subscriber.__init__(self)
        self.subscribe("AccountValue")
    def event(self, event):
        print "receive a data: " + str(event.msg)

sub = StockSubscriber()

o.accountStatus(True)

sub.listen()

print o.getValidIds(1)
print o.getValidIds(2)
print o.getValidIds(3)

# blocked here ...
