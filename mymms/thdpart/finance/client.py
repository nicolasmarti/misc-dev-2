import Pyro.core
from time import sleep
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
import thread


o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

from Pyro.EventService.Clients import Subscriber

def listen():
    sub = ClientSubscriber()
    sub.listen()
    

class ClientSubscriber(Subscriber):
    def __init__(self):
        Subscriber.__init__(self)
        self.subscribe("ContractPrice")
        self.subscribe("ContractSize")
        self.subscribe("OrderStatus")
        self.subscribe("News")
        self.subscribe("ContractDetails")
    def event(self, event):
        print (event.msg)


cid = o.addstock("CS","NYSE","USD")
print "contract := " + str(cid)
activated = o.isActiveContract(cid)
print "is activated := " + str(activated)
if not activated: print "activate := " + str(o.activateContract(cid))
#o.reqNews()
#o.contractDetail(cid)
oid = o.addmktorder("BUY", 1000, "O", cid)
print oid
#thread.start_new_thread(listen, ())
sleep(30)
o.closeOrder(oid)
o.deActivateContract(cid)
#o.cancelNews()

