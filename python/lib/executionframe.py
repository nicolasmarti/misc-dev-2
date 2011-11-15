import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from threading import *
import Pyro.core

from time import *

from accountframe import contract2str

class ExecutionFrame(gtk.Frame, Thread):

    def __init__(self, glock):
        gtk.Frame.__init__(self)
        Thread.__init__(self)
        
        self.glock = glock

        self.set_label("Execution")

        self.table = gtk.Table(100, 100, True)
        self.table.show()
        self.add(self.table)

        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        
        self.liststore = gtk.ListStore(str, str, str, str, str, str)
        self.treeview = gtk.TreeView(self.liststore)

        self.fields = ["contract", "time", "side", "filled", "price", "avgprice"]

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
        
        self.key2iter = dict()


    def run(self):
        o = Pyro.core.getProxyForURI("PYRONAME://serverInterface")
        while True:
            l = o.reqExecutions()                        
            self.glock.acquire()
            gtk.gdk.threads_enter()
            #print "enter execution"
            for d in l:
                key = d[2].m_execId
                if not key in self.key2iter:
                    self.key2iter[key] = self.liststore.append()
                    self.liststore.set_value(self.key2iter[key], 0, contract2str(d[1]))
                    self.liststore.set_value(self.key2iter[key], 1, d[2].m_time)
                    self.liststore.set_value(self.key2iter[key], 2, d[2].m_side)
                    self.liststore.set_value(self.key2iter[key], 3, d[2].m_shares)
                    self.liststore.set_value(self.key2iter[key], 4, d[2].m_price)
                    self.liststore.set_value(self.key2iter[key], 5, d[2].m_avgPrice)
            #print "exit execution"
            gtk.gdk.threads_leave()
            self.glock.release()
            sleep(3)

