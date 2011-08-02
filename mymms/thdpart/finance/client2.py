import Pyro.core
from time import sleep
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message

from Pyro.EventService.Clients import Subscriber

class ClientSubscriber(Subscriber):
    def __init__(self):
        Subscriber.__init__(self)
        #self.subscribe("ContractPrice")
        #self.subscribe("ContractSize")
        #self.subscribe("OrderStatus")
        self.subscribe("News")
    def event(self, event):
        print (event.msg)

sub = ClientSubscriber()
sub.listen()
