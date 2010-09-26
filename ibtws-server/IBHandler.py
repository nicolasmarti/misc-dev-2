# for ib
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

# IB message handler
def error_handler(msg):
    print "error: " + str(msg)

def tick_handler(msg):
    print "tick: " + str(msg)

def order_handler(msg):
    print "order: " + str(msg)

def news_handler(msg):
    print "news: "+ str(msg)    

def contractdet_handler(msg):
    print "contractdet: "+ str(msg)    

def subscriptdata_handler(msg):
    print "suscriptdat: "+ str(msg)    

def subscriptdataend_handler(msg):
    print "suscriptdataend: "+ str(msg)    

def my_account_handler(msg):
    print "account: "+ str(msg)

def watcher(msg):
    print "watcher: " + str(msg)

