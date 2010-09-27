# for ib
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

# IB message handler
class Handler:

    def __init__(self, sp):
        self.m_sp = sp

    def error_handler(self, msg):
        print "error: " + str(msg)

    def tick_handler(self, msg):
        print "tick: " + str(msg)

    def order_handler(self, msg):
        print "order: " + str(msg)

    def news_handler(self, msg):
        print "news: "+ str(msg)    

    def contractdet_handler(self, msg):
        print "contractdet: "+ str(msg)    

    def subscriptdata_handler(self, msg):
        print "suscriptdat: "+ str(msg)    

    def subscriptdataend_handler(self, msg):
        print "suscriptdataend: "+ str(msg)    

    def my_account_handler(self, msg):
        #print "account: "+ str(msg.values())
        self.m_sp.publishAccountInfo(msg.values())

    def watcher(self, msg):
        print "watcher: " + str(msg)

