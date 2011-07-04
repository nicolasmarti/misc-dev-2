import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from threading import *

import Pyro.core
from Pyro.EventService.Clients import Subscriber

class AccountFrame(gtk.Frame, Subscriber):

    def __init__(self, glock):
        gtk.Frame.__init__(self)
        Subscriber.__init__(self)

        self.glock = glock

        self.subscribe("UpdateAccountValue")
        #self.subscribe("UpdatePortfolio")
        #self.subscribe("UpdateAccountTime")

        self.setThreading(0)

        self.set_label("Account")

        self.table = gtk.Table(100, 100, True)
        self.table.show()
        self.add(self.table)

        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        
        self.liststore = gtk.ListStore(str, str, str, str)
        self.treeview = gtk.TreeView(self.liststore)

        self.keycolumn = gtk.TreeViewColumn('Key')
        self.valuecolumn = gtk.TreeViewColumn('Value')
        self.currencycolumn = gtk.TreeViewColumn('Currency')
        self.accountcolumn = gtk.TreeViewColumn('Account')

        self.treeview.append_column(self.keycolumn)
        self.treeview.append_column(self.valuecolumn)
        self.treeview.append_column(self.currencycolumn)
        self.treeview.append_column(self.accountcolumn)

        self.keycell = gtk.CellRendererText()
        self.keycolumn.pack_start(self.keycell, True)
        self.keycolumn.add_attribute(self.keycell, 'text', 0)

        self.valuecell = gtk.CellRendererText()
        self.valuecolumn.pack_start(self.valuecell, True)
        self.valuecolumn.add_attribute(self.valuecell, 'text', 1)

        self.currencycell = gtk.CellRendererText()
        self.currencycolumn.pack_start(self.currencycell, True)
        self.currencycolumn.add_attribute(self.currencycell, 'text', 2)

        self.accountcell = gtk.CellRendererText()
        self.accountcolumn.pack_start(self.accountcell, True)
        self.accountcolumn.add_attribute(self.accountcell, 'text', 3)

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
        if event.subject == "UpdateAccountValue":
            gtk.gdk.threads_enter()
            #print "enter account value"
            key = event.msg[0]
            
            if not key in self.name2iter:
                self.name2iter[key] = self.liststore.append(event.msg)

            self.liststore.set_value(self.name2iter[key], 0, event.msg[0])
            self.liststore.set_value(self.name2iter[key], 1, event.msg[1])
            self.liststore.set_value(self.name2iter[key], 2, event.msg[2])
            self.liststore.set_value(self.name2iter[key], 3, event.msg[3])
            #print "exit account value"
            gtk.gdk.threads_leave() 
        self.glock.release()

def contract2str(c):
    result = ""
    result += c.m_symbol

    if c.m_secType == "STK":
        result += " STK(" + c.m_primaryExch + ")" 
        
    
    if c.m_secType == "OPT" or c.m_secType == "FUT":
        result += " " + c.m_expiry 
    
    if c.m_secType == "OPT":
        result += " " + c.m_right + "Option  " + str(c.m_strike) + " " + c.m_currency
    
    return result
