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

class TWS(Pyro.core.ObjBase, Pyro.EventService.Clients.Publisher, Thread):
    
    def __init__(self, addr, daemon):

        # inheritance init
        Pyro.core.ObjBase.__init__(self)
        Pyro.EventService.Clients.Publisher.__init__(self)
        Thread.__init__(self)

        # data
        # model: 
        # dict id [ lock, -- this element lock
        #           [inittime, timeout, lock] || None, -- the blocking info/control
        #           [State, Data, cancel], -- the state of the request ERROR, FINISHED, INPROGRESS, CANCELLING, CANCELLED, PENDING
        #           PublishingChannel || None, -- publishing info 
        #           DATA -- the data
        #         ]
        self.m_data = dict()
        # global data lock (for inserting, thread traversal)
        self.m_data_lock = Lock()

        # the connection
        self.con = ibConnection(addr)

        # the reqId counter and its lock
        self.reqId = 0
        self.reqId_lock = Lock()

        # thread loop condition
        self.m_terminate = False
        # thread waking up period
        self.m_period = 5

        self.daemon = daemon
        
        # here should follow the handler registration
        self.con.register(self.error_handler, 'Error')
        self.con.register(self.nextValidId, 'NextValidId')
        self.con.register(self.updateAccountValue, 'UpdateAccountValue')
        self.con.register(self.updatePortfolio, 'UpdatePortfolio')
        self.con.register(self.updateAccountTime, 'UpdateAccountTime')

        self.con.registerAll(self.catchall)

        self.con.connect()

        # here some initialization (account, ...)

        self.con.reqAccountUpdates(True, '')

        return

    # get a fresh reqId
    def getFreshReqID(self):
        self.reqId_lock.acquire()
        res = self.reqId
        self.reqId += 1
        self.reqId_lock.release()

    # test
    def isINPROGRESS(self, reqid):
        return self.m_data[reqid][2][1] == "INPROGRESS"

    def isTimeOut(self, reqid):
        if self.m_data[reqid][1] <> None:
            return (now() < self.m_data[reqid][1][0] + self.m_data[reqid][1][1])
        else:
            return False

    def isBlocked(self, reqid):
        if self.m_data[reqid][1] <> None:
            return self.m_data[reqid][1][2].locked()
        else:
            return False

    def isDONE(self, reqid):
        return (self.m_data[reqid][2][1] == "FINISHED" or self.m_data[reqid][2][1] == "CANCELLED" or self.m_data[reqid][2][1] == "ERROR")

    # insert request
    def insertReq(self, timeout=None, channel=None, cancel=None):
        self.m_data_lock.acquire()
        reqid = self.getFreshReqID()        
        self.m_data[reqid] = [Lock(), None, ["PENDING", None, cancel], channel, None]
        if timeout: 
            self.m_data[reqid][1] = [None, timeout, Lock()]
            self.m_data[reqid][1][2].acquire()
        self.m_data_lock.release()
        return reqid

    # start a (maybe blocking) request
    def startReq(self, reqid):
        self.m_data[reqid][0].acquire()     
        self.m_data[reqid][2][0] = "INPROGRESS"
        if self.m_data[reqid][1] <> None: 
            self.m_data[reqid][1][0] = now()
        self.m_data[reqid][0].release()        
        
        if self.m_data[reqid][1] <> None: 
            self.m_data[reqid][1][2].acquire()

    # cancel a request
    def cancelReq(self, reqid):
        self.m_data[reqid][0].acquire()     
        if isINPROGRESS(reqid): 
            self.m_data[reqid][2][0] = "CANCELLING"
            self.m_data[d][2][2](reqid)
        self.m_data[reqid][0].release()        

    # finish a request
    def finishReq(self, reqid):
        self.m_data[reqid][0].acquire()     
        if isINPROGRESS(reqid): 
            self.m_data[reqid][2][0] = "FINISHED"
        self.m_data[reqid][0].release()        

    # error a request
    def errorReq(self, reqid, msg):
        self.m_data[reqid][0].acquire()     
        if isINPROGRESS(reqid): 
            self.m_data[reqid][2][0] = "ERROR"
            self.m_data[reqid][2][1] = msg
        self.m_data[reqid][0].release()        

    # the thread
    def run(self):
        
        while not self.m_terminate:
            sleep(self.m_period)
            self.m_data_lock.acquire()

            for d in self.m_data:
                self.m_data[d][0].acquire()
                
                # still in progress, looking for the timeout
                if self.isINPROGRESS(d) and self.isTimeOut(d):
                    self.m_data[d][2][1] == "CANCELLING"
                    self.m_data[d][2][2](reqid)

                # it's CANCELLED or FINISHED, blocking and still locked
                elif self.isDONE(d) and self.isBlocked(id):
                    self.m_data[reqid][1][2].release()                    

                # else nothing to be done

                self.m_data[d][0].release()

            self.m_data_lock.release()

        return

    # stop the thread
    def stop(self):
        self.m_terminate = True
        return


    def exit(self):
        self.stop()
        self.daemon.disconnect(self)
        os._exit(0)

    # here we should have handlers ...
    # the special error handler
    def error_handler(self, msg):
        #print "error(reqid=" + str(msg.values()[0])+ " ): " + str(msg.values()[2])
        self.errorReq(msg.values()[0], msg.values()[2])

    # next valid id
    def nextValidId(self, msg):
        #print "nextValidId = " + str(msg.values()[0])
        self.reqId_lock.acquire()
        self.reqId = msg.values()[0]
        self.reqId_lock.release()

    # account update
    def updateAccountValue(self, msg):
        #print "update acount value: " + str(msg)
        self.publish("UpdateAccountValue", (msg.values()[0], msg.values()[1], msg.values()[2], msg.values()[3]))

    def updatePortfolio(self, msg):
        #print "update portfolio: " + str(msg)
        self.publish("UpdatePortfolio", (msg.values()[0], msg.values()[1], msg.values()[2], msg.values()[3], msg.values()[4], msg.values()[5], msg.values()[6], msg.values()[7]))

    def updateAccountTime(self, msg):
        #print "update account time: " + str(msg)
        self.publish("UpdateAccountTime", msg.values()[0])


    # catch all
    def catchall(self, msg):
        print str(msg)


    # services
    def reqAccountUpdates(self, flag):
        self.con.reqAccountUpdates(flag, '')        
        
Pyro.core.initServer()
ns=Pyro.naming.NameServerLocator().getNS()
daemon=Pyro.core.Daemon()
daemon.useNameServer(ns)

si = TWS("127.0.0.1", daemon)
uri=daemon.connect(si,"serverInterface")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri

# main loop = listening to pyro defined interface daemon
print "Start main loop"
daemon.requestLoop()
