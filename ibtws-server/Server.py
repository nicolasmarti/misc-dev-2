# Imports

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

    def __init__(self):
        return

    def nextvalidid(self, msg):
        print "nextValidId" + str(msg)

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
        self.m_con.reqAccountUpdates(flag, '')
        return


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

validServer = ValidId()
globalconfig["ValidId"] = validServer
accountServer = AccountServer()
globalconfig["Account"] = accountServer
globalconfig["con"] = con

# registering callbacks
con.register(handler.my_account_handler, 'UpdateAccountValue')
con.register(handler.nextvalidid, "NextValidId")
con.registerAll(handler.watcher)
con.register(validServer.nextvalidid, "NextValidId")

# connection
con.connect()

# register interface
si = ServerInterface(con)
uri=daemon.connect(si,"serverInterface")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri

# main loop = listening to pyro defined interface daemon
daemon.requestLoop()

