import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from threading import *

import Pyro.core
from Pyro.EventService.Clients import Subscriber

from accountframe import contract2str

class PortfolioFrame(gtk.Frame, Subscriber):

    def __init__(self, glock):
        gtk.Frame.__init__(self)
        Subscriber.__init__(self)

        self.glock = glock

        #self.subscribe("UpdateAccountValue")
        self.subscribe("UpdatePortfolio")
        #self.subscribe("UpdateAccountTime")
        
        self.setThreading(0)

        self.set_label("Portfolio")

        self.table = gtk.Table(100, 100, True)
        self.table.show()
        self.add(self.table)

        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        
        self.liststore = gtk.ListStore(str, str, str, str, str, str, str, str)
        self.treeview = gtk.TreeView(self.liststore)

        self.fields = ["contract", "position", "marketprice", "marketvalue", "averageCost", "unrealizedPnL", "realizedPnL", "accountName"]

        self.columns = range(0, len(self.fields))
        self.cells = range(0, len(self.fields))
                            

        for i in range(0, len(self.fields)):
            self.columns[i] = gtk.TreeViewColumn(self.fields[i])
            self.treeview.append_column(self.columns[i])
            self.cells[i] = gtk.CellRendererText()
            self.columns[i].pack_start(self.cells[i], True)
            self.columns[i].add_attribute(self.cells[i], 'text', i)


        self.treeview.show()
        self.sw.add(self.treeview)
        self.sw.show()
        self.table.attach(self.sw, 0, 100, 0, 100)
        
        self.name2iter = dict()

    def loop(self):
        #print "enter loop"
        self.listen()
        #print "exit loop"
        return False

    def event(self, event):
        self.glock.acquire()
        if event.subject == "UpdatePortfolio":
            gtk.gdk.threads_enter()
            #print "enter portfolio"

            key = contract2str(event.msg[0])

            if not key in self.name2iter:
                self.name2iter[key] = self.liststore.append()
                self.liststore.set_value(self.name2iter[key], 0, key)

            for i in range(1, len(self.fields)):
                self.liststore.set_value(self.name2iter[key], i, event.msg[i])

            #print "exit portfolio"
            gtk.gdk.threads_leave()
        self.glock.release()
