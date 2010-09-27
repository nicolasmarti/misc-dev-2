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

#internal
from ServerInterface import *
from ServerPublisher import *
from IBHandler import *

# initialization

# DBMS

# Pyro init (requestloop will be executed at the end of the loop)
Pyro.core.initServer()
ns=Pyro.naming.NameServerLocator().getNS()
daemon=Pyro.core.Daemon()
daemon.useNameServer(ns)

sp = ServerPublisher()

handler = Handler(sp)

# Ib init
con = ibConnection("192.168.0.6")
print con

con.register(handler.tick_handler, message.TickSize)
con.register(handler.tick_handler, message.TickPrice)
con.register(handler.order_handler, message.OrderStatus)
con.register(handler.error_handler, message.Error)
con.register(handler.news_handler, message.UpdateNewsBulletin)
con.register(handler.contractdet_handler, message.ContractDetails)
con.register(handler.subscriptdata_handler, 'ScannerData')
con.register(handler.subscriptdataend_handler, 'ScannerDataEnd')
con.register(handler.my_account_handler, 'UpdateAccountValue')
con.connect()

si = ServerInterface(con)
uri=daemon.connect(si,"serverInterface")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri



# main loop = listening to pyro defined interface daemon
daemon.requestLoop()

