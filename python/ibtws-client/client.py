#!/usr/bin/env python

# example notebook.py

import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from types import *
from threading import *
from time import *
from datetime import *
from pytz import timezone
import pytz
import sys

import Pyro.core
from Pyro.EventService.Clients import Subscriber

from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

from worldclockwindow import *
from evalframe import *
from accountframe import *
from portfolioframe import *
from executionframe import *
from stockframe import *

from gtksheet import *

gtk.gdk.threads_init()


def updateloop():
    while True:
        sleep(200)
    return

def main():
    gtk.gdk.threads_enter()
    gtk.main()
    gtk.gdk.threads_leave()

if __name__ == "__main__":

    glock = Lock()

    notebook = gtk.Notebook()
    notebook.set_tab_pos(gtk.POS_TOP)
    notebook.show()
    
    window = WorldClockWindow(glock)
    window.start()
    window.show()
    window.add(notebook)

    evalf = EvalFrame()
    evalf.show()
    notebook.append_page(evalf, gtk.Label(evalf.get_label()))

    sheetf = gtk.Frame()
    ss = Sheet()
    sheetf.add(ss)
    sheetf.show()
    ss.show()
    notebook.append_page(sheetf, gtk.Label("sheet"))

    accountf = AccountFrame(glock)
    accountf.show()
    th = Thread(target=accountf.loop)
    th.daemon = True
    th.start()
    notebook.append_page(accountf, gtk.Label(accountf.get_label()))
    
    portfoliof = PortfolioFrame(glock)
    portfoliof.show()
    th = Thread(target=portfoliof.loop)
    th.daemon = True
    th.start()
    notebook.append_page(portfoliof, gtk.Label(portfoliof.get_label()))

    executionf = ExecutionFrame(glock)
    executionf.show()
    executionf.daemon = True
    executionf.start()
    notebook.append_page(executionf, gtk.Label(executionf.get_label()))

    stockf = StockFrame(glock, "GS")
    stockf.show()
    stockf.daemon = True
    stockf.start()
    notebook.append_page(stockf, gtk.Label(stockf.get_label()))

    #executionf.start()

    o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")    
    # version 1
    o.accountStatus(True)

    #executionf.start()

    main()
    
    sys.exit(0)
