import pygtk
pygtk.require('2.0')
import gobject 
import gtk

import Pyro.core
from Pyro.EventService.Clients import Subscriber
from threading import *

from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

from time import *

class StockFrame(gtk.Frame, Thread):

    def __init__(self, glock, name):
        gtk.Frame.__init__(self)
        Thread.__init__(self)

        self.daemon = True
        self.glock = glock
        self.stkname = name
        self.set_label("Stock: " + name)

        self.table = gtk.Table(100, 100, True)
        self.table.show()
        self.add(self.table)

        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        self.liststore = gtk.ListStore(str, str, str, str, str, str, str, str, str, str)
        self.treeview = gtk.TreeView(self.liststore)

        self.fields = ["BID SIZE", "BID PRICE", "ASK PRICE", "ASK SIZE", "LAST PRICE", "LAST SIZE", "HIGH", "LOW", "VOLUME", "CLOSE"]

        self.columns = range(0, len(self.fields))
        self.cells = range(0, len(self.fields))

        for i in range(0, len(self.fields)):
            self.columns[i] = gtk.TreeViewColumn(self.fields[i])
            self.treeview.append_column(self.columns[i])
            self.cells[i] = gtk.CellRendererText()
            self.columns[i].pack_start(self.cells[i], True)
            self.columns[i].add_attribute(self.cells[i], 'text', i)


        self.mktdatakey = self.liststore.append()

        self.treeview.show()
        self.sw.add(self.treeview)
        self.sw.show()
        self.table.attach(self.sw, 0, 100, 0, 20)

        # should have a class for that ...

        self.sw2 = gtk.ScrolledWindow()
        self.sw2.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        self.liststore2 = gtk.ListStore(str, str)
        self.treeview2 = gtk.TreeView(self.liststore2)

        self.fields2 = ["ASK PRICE", "ASK SIZE"]

        self.columns2 = range(0, len(self.fields2))
        self.cells2 = range(0, len(self.fields2))

        for i in range(0, len(self.fields2)):
            self.columns2[i] = gtk.TreeViewColumn(self.fields2[i])
            self.treeview2.append_column(self.columns2[i])
            self.cells2[i] = gtk.CellRendererText()
            self.columns2[i].pack_start(self.cells2[i], True)
            self.columns2[i].add_attribute(self.cells2[i], 'text', i)

        self.key2iter = None

        self.treeview2.show()
        self.sw2.add(self.treeview2)
        self.sw2.show()
        self.table.attach(self.sw2, 0, 20, 21, 80)

        # should have a class for that ...

        self.sw3 = gtk.ScrolledWindow()
        self.sw3.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        self.liststore3 = gtk.ListStore(str, str)
        self.treeview3 = gtk.TreeView(self.liststore3)

        self.fields3 = ["BID PRICE", "BID SIZE"]

        self.columns3 = range(0, len(self.fields3))
        self.cells3 = range(0, len(self.fields3))

        for i in range(0, len(self.fields3)):
            self.columns3[i] = gtk.TreeViewColumn(self.fields3[i])
            self.treeview3.append_column(self.columns3[i])
            self.cells3[i] = gtk.CellRendererText()
            self.columns3[i].pack_start(self.cells3[i], True)
            self.columns3[i].add_attribute(self.cells3[i], 'text', i)

        self.key2iter2 = None

        self.treeview3.show()
        self.sw3.add(self.treeview3)
        self.sw3.show()
        self.table.attach(self.sw3, 21, 41, 21, 80)


    def run(self):

        o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")

        c = Contract()
        c.m_symbol = self.stkname
        c.m_secType = "STK"

        c = o.reqContractDetails(c)[0].m_summary

        print "Market Ticker: " + c.m_symbol + ", secType:" + c.m_secType + ", exchange: " + c.m_exchange + ", currency: " + c.m_currency

        mktDataId= o.reqMktData(c, False)
        mktDepthId = o.reqMktDepth(c, 10)

        while True:
            self.glock.acquire()

            gtk.gdk.threads_enter()

            data = o.getMktData(mktDataId)
            if (len(data.keys())) == len(self.fields):
                for i in range(0, len(self.fields) - 1):
                    #print "keys := " + str(data.keys())
                    #print "data[" + str(self.fields[i]) + "] = " + str(data[self.fields[i]])
                    self.liststore.set_value(self.mktdatakey, i, str(data[self.fields[i]]))

            #print str(data)

            depth = o.getMktDepth(mktDepthId)

            if self.key2iter == None:
                self.key2iter = [ self.liststore2.append() for i in depth[0] ] 

            if self.key2iter2 == None:
                self.key2iter2 = [ self.liststore3.append() for i in depth[1] ] 

            for i in range(0, len(depth[0])):
                if depth[0][i] == None:
                    self.liststore2.set_value(self.key2iter[i], 0, "--")
                    self.liststore2.set_value(self.key2iter[i], 1, "--")
                else:
                    self.liststore2.set_value(self.key2iter[i], 0, str(depth[0][i][0]))
                    self.liststore2.set_value(self.key2iter[i], 1, str(depth[0][i][1]))


            for i in range(0, len(depth[1])):
                if depth[1][i] == None:
                    self.liststore3.set_value(self.key2iter2[i], 0, "--")
                    self.liststore3.set_value(self.key2iter2[i], 1, "--")
                else:
                    self.liststore3.set_value(self.key2iter2[i], 0, str(depth[1][i][0]))
                    self.liststore3.set_value(self.key2iter2[i], 1, str(depth[1][i][1]))

            gtk.gdk.threads_leave()
            self.glock.release()
            sleep(1)

