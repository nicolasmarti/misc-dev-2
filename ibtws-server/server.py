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

si = ServerInterface()
uri=daemon.connect(si,"serverInterface")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri

sp = ServerPublisher()

# Ib init
con = ibConnection("192.168.0.3")
print con
#con.registerAll(watcher)
con.register(tick_handler, message.TickSize)
con.register(tick_handler, message.TickPrice)
con.register(order_handler, message.OrderStatus)
con.register(error_handler, message.Error)
con.register(news_handler, message.UpdateNewsBulletin)
con.register(contractdet_handler, message.ContractDetails)
con.register(subscriptdata_handler, 'ScannerData')
con.register(subscriptdataend_handler, 'ScannerDataEnd')
con.register(my_account_handler, 'UpdateAccountValue')
con.connect()
#con.reqAccountUpdates(1, '')

# main loop = listening to pyro defined interface daemon
daemon.requestLoop()

