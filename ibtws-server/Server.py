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
        self.m_nextid = 0
        return

    def getNextId(self):
        self.m_lock.acquire()
        res = self.m_nextid
        self.m_nextid += 1
        self.m_lock.release()
        return res

    # nextID
    def handler1(self, msg):
        self.m_lock.acquire()
        #print "nextValidId: " + str(msg.values())
        self.m_nextid = msg.values()[0] # where to get it?
        self.m_lock.release()


class AccountServer(Pyro.EventService.Clients.Publisher):

    def __init__(self, con):
        Pyro.EventService.Clients.Publisher.__init__(self)
        self.m_con = con
        return

    def handler1(self, msg):
        #print "update acount value: " + str(msg)
        self.publish("UpdateAccountValue", msg)

    def handler2(self, msg):
        #print "update portfolio: " + str(msg)
        self.publish("UpdatePortfolio", msg)

    def handler3(self, msg):
        #print "update account time: " + str(msg)
        self.publish("UpdateAccountTime", msg)

class OrderServer(Pyro.EventService.Clients.Publisher, Thread):

    def __init__(self, con, nextId, serverC):
        Pyro.EventService.Clients.Publisher.__init__(self)
        self.m_con = con
        self.m_nextId = nextId
        self.m_serverC = serverC

        self.inProgressOrders = dict()
        self.inProgressOrdersLock = Lock()

        self.doneOrders = dict()
        self.doneOrdersLock = Lock()

        Thread.__init__(self)
        self.m_loop = True

        return

    # timeout = None -> non blocking
    # else -> blocking
    def placeOrder(self, contract, order, timeout):

        oid = self.m_nextId.getNextId()
        order.m_orderId = oid
        order.m_transmit = True

        self.m_serverC.registerId(oid, self.error)

        self.inProgressOrdersLock.acquire()
        self.inProgressOrders[oid] = [[contract, order], [oid, "PendingSubmit"], None, [timeout, date.today()], Lock()]
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

    def error(self, oid):
        self.inProgressOrdersLock.acquire()
        if oid in self.inProgressOrders:
            self.inProgressOrders[oid][1] = [oid, "Error"]
        self.inProgressOrdersLock.release()
        
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
                    if self.inProgressOrders[k][1] <> None and (self.inProgressOrders[k][1][1] == "Cancelled" or self.inProgressOrders[k][1][1] == "Filled" or self.inProgressOrders[k][1][1] == "ApiCancelled"):
                        print "done"
                        self.doneOrders[k] = self.inProgressOrders[k]
                        del self.inProgressOrders[k]
                        if self.doneOrders[k][4].locked(): self.doneOrders[k][4].release()
                        changed = True

            self.inProgressOrdersLock.release()

    def stop(self):
        self.m_loop = False

    # order status
    def handler2(self, msg):
        #print "order Status: " + str(msg.values())
        self.inProgressOrdersLock.acquire()
        if msg.values()[0] in self.inProgressOrders:
            self.inProgressOrders[msg.values()[0]][1]=msg.values()
        else:
            self.inProgressOrders[msg.values()[0]] = [[None, None], msg.values(), None, [None, date.today()], Lock()]            
        self.inProgressOrdersLock.release()

    # open Order
    def handler3(self, msg):
        #print "open Order: " + str(msg.values())
        self.inProgressOrdersLock.acquire()
        if msg.values()[0] in self.inProgressOrders:
            self.inProgressOrders[msg.values()[0]][2]=msg.values()[3]
        else:
            self.inProgressOrders[msg.values()[0]] = [[msg.values()[1], msg.values()[2]], None, msg.values()[3], [None, date.today()], Lock()]            
            
        self.inProgressOrdersLock.release()

# Market Scanner
class ScannerServer:
    def __init__(self, con, idServer, conServer):
        self.m_con = con
        self.m_idServer = idServer
        self.m_conServer = conServer

        self.m_reqHandler = dict()
        self.m_reqHandlerLock = Lock()

 
    def mktScan(self, scannerInfo):
        scanid = self.m_idServer.getNextId()
        self.m_reqHandlerLock.acquire()         
        self.m_reqHandler[scanid] = [Lock(), dict()]
        self.m_reqHandler[scanid][0].acquire()
        self.m_reqHandlerLock.release()         
        self.m_conServer.registerId(scanid, self.error)
        con.reqScannerSubscription(scanid, scannerInfo) 
        self.m_reqHandler[scanid][0].acquire()
        return self.m_reqHandler[scanid][1]

    def error(self, tid):
        self.m_reqHandlerLock.acquire()         
        if self.m_reqHandler[tid][0].locked(): self.m_reqHandler[tid][0].release()
        self.m_reqHandlerLock.release()

    def handler1(self, msg):
        #print "scanner data: " + str(msg)
        
        self.m_reqHandlerLock.acquire()
        self.m_reqHandler[msg.values()[0]][1][msg.values()[1]] = (msg.values()[2], msg.values()[3], msg.values()[4], msg.values()[5], msg.values()[6])
        self.m_reqHandlerLock.release()

    def handler2(self, msg):
        #print "scanner data end: " + str(msg)        
        self.m_reqHandlerLock.acquire()
        if self.m_reqHandler[msg.values()[0]][0].locked(): self.m_reqHandler[msg.values()[0]][0].release()
        self.m_reqHandlerLock.release()

    def handler3(self, msg):
        print "scanner Param: " + str(msg)        

# MktData Server

class MktDataServer:
    
    def __init__(self, con, idServer, conServer):
        self.m_con = con
        self.m_idServer = idServer
        self.m_conServer = conServer

        self.m_dataHandler = dict()
        self.m_dataHandlerLock = Lock()

        self.m_tick = ["BID SIZE", "BID PRICE", "ASK PRICE", "ASK SIZE", "LAST PRICE", "LAST SIZE", "HIGH", "LOW", "VOLUME", "CLOSE"]

    def reqMktData(self, contract, oneshot):
        dataid = self.m_idServer.getNextId()
        self.m_dataHandlerLock.acquire()
        self.m_dataHandler[dataid] = [dict(), dict()]
        self.m_dataHandlerLock.release()
        self.m_con.reqMktData(dataid, contract, '', oneshot)
        return dataid

    def cancelMktData(self, dataid):
        self.m_con.cancelMktData(dataid)

    def getMktData(self, dataid):
        self.m_dataHandlerLock.acquire()
        if dataid in self.m_dataHandler:
            res = self.m_dataHandler[dataid][0]
        else:
            res = None
        self.m_dataHandlerLock.release()
        return res

    # tickPrice/tickSize
    def handler1(self, msg):
        #print "tickPrice/Size: " + str(msg.values())
        self.m_dataHandlerLock.acquire()
        self.m_dataHandler[msg.values()[0]][0][self.m_tick[msg.values()[1]]] = msg.values()[2]            
        self.m_dataHandlerLock.release()

# MktDepth Server

class MktDepthServer:
    
    def __init__(self, con, idServer, conServer):
        self.m_con = con
        self.m_idServer = idServer
        self.m_conServer = conServer

        self.m_dataHandler = dict()
        self.m_dataHandlerLock = Lock()

    def reqMktDepth(self, contract, numrows):
        dataid = self.m_idServer.getNextId()
        self.m_dataHandlerLock.acquire()
        self.m_dataHandler[dataid] = [None for i in range(0, numrows)]
        self.m_dataHandlerLock.release()
        self.m_con.reqMktDepth(dataid, contract, numrows)
        return dataid

    def cancelMktDepth(self, dataid):
        self.m_con.cancelMktDepth(dataid)

    def getMktDepth(self, dataid):
        self.m_dataHandlerLock.acquire()
        if dataid in self.m_dataHandler:
            res = self.m_dataHandler[dataid]
        else:
            res = None
        self.m_dataHandlerLock.release()
        return res

    # updateMktDepth
    def handler1(self, msg):
        print "updateMktDepth: " + str(msg.values())
        self.m_dataHandlerLock.acquire()
        if msg.values()[2] == 0 or msg.values()[2] == 1:
            self.m_dataHandler[msg.values()[0]][msg.values()[1]] = (msg.values()[3], msg.values()[4], msg.values()[5])
        elif msg.values()[2] == 2:
            self.m_dataHandler[msg.values()[0]][msg.values()[1]] = None
        self.m_dataHandlerLock.release()

    # updateMktDepthL2
    def handler2(self, msg):
        print "updateMktDepthL2: " + str(msg.values())
        self.m_dataHandlerLock.acquire()
        if msg.values()[3] == 0 or msg.values()[3] == 1:
            self.m_dataHandler[msg.values()[0]][msg.values()[1]] = (msg.values()[2], msg.values()[4], msg.values()[5], msg.values()[6])
        elif msg.values()[3] == 2:
            self.m_dataHandler[msg.values()[0]][msg.values()[1]] = None
        self.m_dataHandlerLock.release()


# server object
class ServerConnection:

    def __init__(self, con):
        self.m_con = con
        self.m_error = dict()
        self.m_errorLock = Lock()

    def registerId(self, tid, fct):
        self.m_errorLock.acquire()
        self.m_error[tid] = fct
        self.m_errorLock.release()

    def handler1(self, msg):
        print "winError: " + str(msg)

    def handler2(self, msg):
        print "error: " + str(msg)
        if msg.values()[0] in self.m_error:
           self.m_error[msg.values()[0]](msg.values()[0])

    def handler3(self, msg):
        print "connectionClosed: " + str(msg)

    def handler4(self, msg):
        print "currentTime: " + str(msg)



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

    def getNextId(self):
        return self.m_config["NextId"].getNextId()

    # order
    def placeOrder(self, contract, order, timeout):
        return self.m_config["Order"].placeOrder(contract, order, timeout)

    def orderStatus(self, oid):
        return self.m_config["Order"].orderStatus(oid)

    def cancelOrder(self, oid):
        self.m_config["con"].cancelOrder(oid)

    # scan
    def scanMkt(self, scanInfo):
        return self.m_config["Scanner"].mktScan(scanInfo)

    def scanParam(self):
        self.m_config["con"].reqScannerParameters()

    # mktData
    def reqMktData(self, contract, oneshot):
        return self.m_config["MktData"].reqMktData(contract, oneshot)

    def cancelMktData(self, dataid):
        self.m_config["MktData"].cancelMktData(dataid)

    def getMktData(self, dataid):
        return self.m_config["MktData"].getMktData(dataid)

    # mktDepth
    def reqMktDepth(self, contract, numrows):
        return self.m_config["MktDepth"].reqMktDepth(contract, numrows)

    def cancelMktDepth(self, dataid):
        self.m_config["MktDepth"].cancelMktDepth(dataid)

    def getMktDepth(self, dataid):
        return self.m_config["MktDepth"].getMktDepth(dataid)

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
con = ibConnection("192.168.0.4")

#config
globalconfig = dict()

globalconfig["Server"] = ServerConnection(con)

globalconfig["NextId"] = NextIdServer(con)
globalconfig["Account"] = AccountServer(con)
globalconfig["Order"] = OrderServer(con, globalconfig["NextId"], globalconfig["Server"])
globalconfig["Scanner"] = ScannerServer(con, globalconfig["NextId"], globalconfig["Server"])
globalconfig["MktData"] = MktDataServer(con, globalconfig["NextId"], globalconfig["Server"])
globalconfig["MktDepth"] = MktDepthServer(con, globalconfig["NextId"], globalconfig["Server"])
globalconfig["con"] = con
globalconfig["daemon"] = daemon

# just for debug
def watcher(msg):
    print "watcher: " + str(msg)

# registering callbacks
con.register(globalconfig["NextId"].handler1, "NextValidId")

con.register(globalconfig["Account"].handler1, 'UpdateAccountValue')
con.register(globalconfig["Account"].handler2, 'UpdatePortfolio')
con.register(globalconfig["Account"].handler3, 'UpdateAccountTime')

con.register(globalconfig["Order"].handler2, message.OrderStatus)
con.register(globalconfig["Order"].handler3, message.OpenOrder)

con.register(globalconfig["Scanner"].handler1, 'ScannerData')
con.register(globalconfig["Scanner"].handler2, 'ScannerDataEnd')
con.register(globalconfig["Scanner"].handler3, 'ScannerParameters')

con.register(globalconfig["MktData"].handler1, 'TickPrice')
con.register(globalconfig["MktData"].handler1, 'TickSize')

con.register(globalconfig["MktDepth"].handler1, message.UpdateMktDepth)
con.register(globalconfig["MktDepth"].handler2, message.UpdateMktDepthL2)

con.register(globalconfig["Server"].handler1, 'WinError')
con.register(globalconfig["Server"].handler2, 'Error')
con.register(globalconfig["Server"].handler3, 'ConnectionClosed')
con.register(globalconfig["Server"].handler4, 'CurentTime')

con.registerAll(watcher)

# connection
con.connect()



# register interface
si = ServerInterface(globalconfig)
uri=daemon.connect(si,"serverInterface")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri

# main loop = listening to pyro defined interface daemon
print "Start main loop"
daemon.requestLoop()

