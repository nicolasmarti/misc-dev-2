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

gtk.gdk.threads_init()

class WorldClockWindow(gtk.Window, Thread):

    def __init__(self, glock):
        gtk.Window.__init__(self)
        Thread.__init__(self)
        
        self.glock = glock
        self.connect("delete_event", self.delete)
        self.set_border_width(10)

        self.daemon = True
        self.set_size_request(800, 400)

    def run(self):
        l = [(timezone('US/Eastern'), "NY"), 
             (timezone('Europe/London'), "London"), 
             (timezone('Europe/Paris'), "Paris"), 
             (timezone('Asia/Singapore'), "HK"), 
             (timezone('Asia/Tokyo'), "Tokyo")]
        while True:
            mstr = ""
            for d in l:
                mnow = datetime.now(d[0])
                mstr += d[1] + mnow.strftime(" %d/%m/%Y %H:%M:%S   ")
            self.glock.acquire()
            gtk.gdk.threads_enter()
            #print "enter time"
            self.set_title(mstr)
            #print "exit time"
            gtk.gdk.threads_leave()
            self.glock.release()
            sleep(1)
        return False

    def delete(self, widget, event=None):
        gtk.main_quit()
        return False

class EvalFrame(gtk.Frame, Thread):
    
    def __init__(self):
        gtk.Frame.__init__(self)
        self.set_label("Evaluator")
        
        # build a table to put all my stuffs
        self.table = gtk.Table(12, 16, True)
        self.table.show()
        self.add(self.table)

        # build scrolled window and textview
        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        self.textview = gtk.TextView()
        self.textbuffer = self.textview.get_buffer()
        self.sw.add(self.textview)
        self.sw.show()
        self.textview.show()
        self.table.attach(self.sw, 0, 10, 0, 8)

        # build the result textview
        self.sw2 = gtk.ScrolledWindow()
        self.sw2.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        self.textview2 = gtk.TextView()
        self.textview2.set_editable(False)
        self.textbuffer2 = self.textview2.get_buffer()
        self.textview2.show()
        self.sw2.add(self.textview2)
        self.sw2.show()
        self.table.attach(self.sw2, 0, 10, 9, 12)

        # the button
        self.button = gtk.Button(label="execute(F5)")
        self.button.show()
        self.table.attach(self.button, 3, 6, 8, 9)
        self.button.connect("clicked", self.myexec, None)

        self.button = gtk.Button(label="eval(F6)")
        self.button.show()
        self.table.attach(self.button, 0, 3, 8, 9)
        self.button.connect("clicked", self.myeval, None)

        self.button = gtk.Button(label="???")
        self.button.show()
        self.table.attach(self.button, 6, 10, 8, 9)

        self.m_locals = locals()

        # tree view
        self.sw3 = gtk.ScrolledWindow()
        self.sw3.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        self.treestore = gtk.TreeStore(str)
        self.treeview = gtk.TreeView(self.treestore)
        self.tvcolumn = gtk.TreeViewColumn('local name')
        self.treeview.append_column(self.tvcolumn)
        self.treeview.connect("row-activated", self.local_clicked, None)
        self.cell = gtk.CellRendererText()
        self.tvcolumn.pack_start(self.cell, True)
        self.tvcolumn.add_attribute(self.cell, 'text', 0)
        self.sw3.add(self.treeview)
        self.table.attach(self.sw3, 10,16, 0, 12)
        self.sw3.show()
        self.treeview.show()

        self.name2iter = dict()

        for d in self.m_locals:
            iter = self.treestore.append(None, [d])
            self.name2iter[d] = iter

        self.connect("key_press_event", self.key_pressed, None)

    def key_pressed(self, widget, event, data=None):
        if event.keyval == 65474:
            self.myexec(widget)
        elif event.keyval == 65475:
            self.myeval(widget)

        self.textview.grab_focus()

    def myexec(self, widget, data=None):
        m_str = self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())
        try:
            exec m_str in globals(), self.m_locals
            self.textbuffer2.set_text("")        
            self.m_start = self.textbuffer.get_end_iter()
            self.textbuffer.set_text("")
        except BaseException as e:
            self.textbuffer2.set_text(str(e))        

        # is there new vars ?
        for d in self.m_locals:
            if not d in self.name2iter.keys():
                # a new local var
                iter = self.treestore.append(None, [d])
                self.name2iter[d] = iter

        for d in self.name2iter.keys():
            if not d in self.m_locals:
                # remove the var
                self.treestore.remove(self.name2iter[d])
                
        self.textview.grab_focus()

    def myeval(self, widget, data=None):
        m_str = self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())
        try:

            self.textbuffer2.set_text(str(eval(m_str, globals(), self.m_locals)))        
            self.m_start = self.textbuffer.get_end_iter()
            self.textbuffer.set_text("")

        except BaseException as e:
            self.textbuffer2.set_text(str(e))        

            self.textview.grab_focus()

    def local_clicked(self, treeview, path, viewcolumn, data):
        #print "treeview: " + str(treeview) + " :: " + str(type(treeview))
        #print "path: " + str(path) + " :: " + str(type(path))
        #print "viewcolumn: " + str(viewcolumn) + " :: " + str(type(viewcolumn))
        #print "data: " + str(data) + " :: " + str(type(data))

        piter = treeview.get_model().get_iter(path)
        varname = str(treeview.get_model().get_value(piter, 0))
        self.textbuffer.insert(self.textbuffer.get_end_iter(), varname)
        self.textview.grab_focus()

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
            data = o.getMktData(mktDataId)
            print str(data)
            depth = o. getMktDepth(mktDepthId)
            print str(depth)
            self.glock.release()
            sleep(1)


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

    #evalf = EvalFrame()
    #evalf.show()
    #notebook.append_page(evalf, gtk.Label(evalf.get_label()))

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

    stockf = StockFrame(glock, "STAN")
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
