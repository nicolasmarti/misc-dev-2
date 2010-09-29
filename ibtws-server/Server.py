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

class ValidIdServer:

    def __init__(self, con):
        self.m_con = con
        self.m_lock = Lock()
        self.m_id = 0
        return

    def getIds(self, nbids):
        self.m_lock.acquire()
        res = self.m_id
        self.m_id += nbids
        self.m_lock.release()
        return res

    def handler(self, msg):
        self.m_lock.acquire()
        print "nextValidId" + str(msg)
        self.m_id = msg.values()[0] # where to get it?
        self.m_lock.release()

class AccountServer(Pyro.EventService.Clients.Publisher):

    def __init__(self, con):
        Pyro.EventService.Clients.Publisher.__init__(self)
        self.m_con = con
        return

    def handler(self, msg):
        print "acount info: " + str(msg)
        self.publish("AccountValue", msg)

# Interface

# the object exposed through pyro
class ServerInterface(Pyro.core.ObjBase):

    def __init__(self, config):
        Pyro.core.ObjBase.__init__(self)
        self.m_config = config

    # account information
    # flag = true: ignite the flow of data
    # flag = false: stop the flow of data
    def accountStatus(self, flag):
        self.m_config["con"].reqAccountUpdates(flag, '')
        return

    def getValidIds(self, nbids):
        return self.m_config["ValidId"].getIds(nbids)

    # Exit

    def exit(self):
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

validServer = ValidIdServer(con)
globalconfig["ValidId"] = validServer
accountServer = AccountServer(con)
globalconfig["Account"] = accountServer
globalconfig["con"] = con

# registering callbacks
con.register(accountServer.handler, 'UpdateAccountValue')
con.register(validServer.handler, "NextValidId")

# connection
con.connect()

# register interface
si = ServerInterface(globalconfig)
uri=daemon.connect(si,"serverInterface")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri

# main loop = listening to pyro defined interface daemon
daemon.requestLoop()

