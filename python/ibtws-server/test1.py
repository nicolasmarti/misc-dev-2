import Pyro.core
import time

from Pyro.EventService.Clients import Subscriber

o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

class StockSubscriber(Subscriber):
    def __init__(self):
        Subscriber.__init__(self)
        self.subscribe("UpdateAccountValue")
        self.subscribe("UpdatePortfolio")
        self.subscribe("UpdateAccountTime")

    def event(self, event):
        print "receive a data: " + str(event)

sub = StockSubscriber()

o.accountStatus(True)

sub.listen()

# blocked here ...
