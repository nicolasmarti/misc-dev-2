import Pyro.core
import time

from Pyro.EventService.Clients import Subscriber

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

class StockSubscriber(Subscriber):
    def __init__(self):
        Subscriber.__init__(self)
        self.subscribe("NewBulletins")

    def event(self, event):
        print "receive a news: " + str(event)

sub = StockSubscriber()

o.reqNewsBulletins(True)

sub.listen()

# blocked here ...
