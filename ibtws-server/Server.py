# Imports

# for thread lock
from threading import *

# for time-related functions
from time import *
from datetime import *

# general
import sys
import os

# for ib
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

# for pyro
import Pyro.core
import Pyro.naming
import Pyro.constants
import Pyro.EventService.Clients

# Back Servers

class NextIdServer:

    def __init__(self, con):
        self.m_con = con
        self.m_lock = Lock()
        self.m_ids = dict()
        return

    def getNextId(self, category):
        self.m_lock.acquire()
        if category in self.m_ids:
            res = self.m_ids[category]
            self.m_ids[category] += 1
        else:
            res = 0
            self.m_ids[category] = 1
        self.m_lock.release()
        return res


class AccountServer(Pyro.EventService.Clients.Publisher):

    def __init__(self, con):
        Pyro.EventService.Clients.Publisher.__init__(self)
        self.m_con = con
        return

    def handler(self, msg):
        print "acount info: " + str(msg)
        self.publish("AccountValue", msg)

class OrderServer(Pyro.EventService.Clients.Publisher, Thread):

    def __init__(self, con):
        Pyro.EventService.Clients.Publisher.__init__(self)
        self.m_con = con

        self.m_nextid = 0
        self.m_nextidLock = Lock()
        
        self.inProgressOrders = dict()
        self.inProgressOrdersLock = Lock()

        self.doneOrders = dict()
        self.doneOrdersLock = Lock()

        Thread.__init__(self)
        self.m_loop = True

        return

    def nextId(self):
        self.m_nextidLock.acquire()
        res = self.m_nextid
        self.m_nextid += 1        
        self.m_nextidLock.release()
        return res

    # timeout = None -> non blocking
    # else -> blocking
    def placeOrder(self, contract, order, timeout):

        oid = self.nextId()
        order.m_orderId = oid
        order.m_transmit = True

        self.inProgressOrdersLock.acquire()
        self.inProgressOrders[oid] = [(contract, order), [oid, "PendingSubmit"], None, [timeout, date.today()], Lock()]
        self.inProgressOrdersLock.release()

        if timeout == None:
            self.m_con.placeOrder(oid, contract, order)
            return(oid)
        else:
            self.m_con.placeOrder(oid, contract, order)
            self.inProgressOrders[oid][4].acquire()
            self.inProgressOrders[oid][4].acquire()
            # next time I return, the order is in 
            res = self.doneOrders[oid]
            if res[1][2] == 0:
                return None
            else:
                return oid
        
    def orderStatus(self, orderId):
        self.inProgressOrdersLock.acquire()
        if orderId in self.inProgressOrders:
            res = self.inProgressOrders[orderId][1]
            self.inProgressOrdersLock.release()
            return res
        else:
            self.inProgressOrdersLock.release()
            if orderId in self.doneOrders:
                return self.doneOrders[orderId][1]
            else:
                return None


        
    # loop that look at order in progress
    # Cancel, Filled -> put in done, look for time out and possibly unlock
    # other -> look for time out, if timed out, timeout = 0, and cancel the order
    def run(self):

        while self.m_loop:
            changed = False
            sleep(5)
            self.inProgressOrdersLock.acquire()

            l = self.inProgressOrders.keys()

            for k in l:

                if changed: continue

                if self.inProgressOrders[k][3][0] <> None and self.inProgressOrders[k][3][0] + self.inProgressOrders[k][3][1] >= date.today():
                    print "timed out"
                    self.inProgressOrders[k][3][0] = None
                    if self.inProgressOrders[k][1][1] == "PendingSubmit": self.inProgressOrders[k][1][1] == "PendingCancel"
                    self.m_con.cancelOrder(k)
                else:
                    if self.inProgressOrders[k][1] <> None and (self.inProgressOrders[k][1][1] == "Cancelled" or self.inProgressOrders[k][1][1] == "Filled"):
                        print "done"
                        self.doneOrders[k] = self.inProgressOrders[k]
                        del self.inProgressOrders[k]
                        if self.doneOrders[k][4].locked(): self.doneOrders[k][4].release()
                        changed = True

            self.inProgressOrdersLock.release()

    def stop(self):
        self.m_loop = False

    # nextID
    def handler1(self, msg):
        self.m_nextidLock.acquire()
        print "nextValidId: " + str(msg.values())
        self.m_nextid = msg.values()[0] # where to get it?
        self.m_nextidLock.release()

    # order status
    def handler2(self, msg):
        print "order Status: " + str(msg.values())
        self.inProgressOrdersLock.acquire()
        self.inProgressOrders[msg.values()[0]][1]=msg.values()
        self.inProgressOrdersLock.release()

    # open Order
    def handler3(self, msg):
        print "open Status: " + str(msg.values()[3])
        self.inProgressOrdersLock.acquire()
        self.inProgressOrders[msg.values()[0]][2]=msg.values()[3]
        self.inProgressOrdersLock.release()


# Interface

# the object exposed through pyro
class ServerInterface(Pyro.core.ObjBase):

    def __init__(self, config):
        Pyro.core.ObjBase.__init__(self)
        self.m_config = config

        # order
        self.m_config["Order"].start()
        self.m_config["con"].reqAllOpenOrders()

    # account information
    # flag = true: ignite the flow of data
    # flag = false: stop the flow of data
    def accountStatus(self, flag):
        self.m_config["con"].reqAccountUpdates(flag, '')
        return

    def getNextId(self, category):
        return self.m_config["NextId"].getNextId(category)

    # order
    def placeOrder(self, contract, order, timeout):
        return self.m_config["Order"].placeOrder(contract, order, timeout)

    def orderStatus(self, oid):
        return self.m_config["Order"].orderStatus(oid)

    def cancelOrder(self, oid):
        self.m_config["con"].cancelOrder(oid)

    # Exit

    def exit(self):
        self.m_config["Order"].stop()
        self.m_config["daemon"].disconnect(self)
        os._exit(0)


# initialization

# Pyro init (requestloop will be executed at the end of the loop)
Pyro.core.initServer()
ns=Pyro.naming.NameServerLocator().getNS()
daemon=Pyro.core.Daemon()
daemon.useNameServer(ns)

# Ib init
con = ibConnection("192.168.0.2")

#config
globalconfig = dict()

globalconfig["NextId"] = NextIdServer(con)
globalconfig["Account"] = AccountServer(con)
globalconfig["Order"] = OrderServer(con)
globalconfig["con"] = con
globalconfig["daemon"] = daemon

# registering callbacks
con.register(globalconfig["Account"].handler, 'UpdateAccountValue')
con.register(globalconfig["Order"].handler1, "NextValidId")
con.register(globalconfig["Order"].handler2, message.OrderStatus)
con.register(globalconfig["Order"].handler3, message.OpenOrder)

# connection
con.connect()

# register interface
si = ServerInterface(globalconfig)
uri=daemon.connect(si,"serverInterface")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri

# main loop = listening to pyro defined interface daemon
daemon.requestLoop()

