#!/usr/bin/env python

# example notebook.py

import pygtk
pygtk.require('2.0')
import gtk
from types import *

class MyNotebook:

    def delete(self, widget, event=None):
        gtk.main_quit()
        return False

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


    def addframe(self, name):
        frame = gtk.Frame(name)
        frame.set_border_width(10)
        frame.set_size_request(800, 400)
        frame.show()
        label = gtk.Label(name)
        self.notebook.append_page(frame, label)        
        return frame

    def local_clicked(self, treeview, path, viewcolumn, data):
        #print "treeview: " + str(treeview) + " :: " + str(type(treeview))
        #print "path: " + str(path) + " :: " + str(type(path))
        #print "viewcolumn: " + str(viewcolumn) + " :: " + str(type(viewcolumn))
        #print "data: " + str(data) + " :: " + str(type(data))

        piter = treeview.get_model().get_iter(path)
        varname = str(treeview.get_model().get_value(piter, 0))
        self.textbuffer.insert(self.textbuffer.get_end_iter(), varname)
        self.textview.grab_focus()

    def __init__(self):
        self.window = gtk.Window(gtk.WINDOW_TOPLEVEL)
        self.window.connect("delete_event", self.delete)
        self.window.set_border_width(10)


        # Create a new notebook, place the position of the tabs
        self.notebook = gtk.Notebook()
        self.notebook.set_tab_pos(gtk.POS_TOP)
        self.notebook.show()
        self.window.add(self.notebook)

        # the initial page: a raw interp
        bufferf = "myREPL frame"
        bufferl = "myREPL"

        # build frame
        self.frame = gtk.Frame(bufferf)
        self.frame.set_border_width(10)
        self.frame.set_size_request(800, 400)
        self.frame.show()
        self.label = gtk.Label(bufferf)
        self.notebook.append_page(self.frame, self.label)
        
        # build a table to put all my stuffs
        self.table = gtk.Table(12, 16, True)
        self.table.show()
        self.frame.add(self.table)

        # build scrolled window and textview
        self.sw = gtk.ScrolledWindow()
        self.sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        self.textview = gtk.TextView()
        self.textbuffer = self.textview.get_buffer()
        self.sw.add(self.textview)
        self.sw.show()
        self.textview.show()
        self.table.attach(self.sw, 0, 10, 0, 8)

        self.m_start = self.textbuffer.get_start_iter()

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

        self.sw.connect("key_press_event", self.key_pressed, None)

        # another frame, for testing liststore
        self.frame2 = gtk.Frame("liststore")
        self.frame2.set_border_width(10)
        self.frame2.set_size_request(800, 400)
        self.frame2.show()
        self.notebook.append_page(self.frame2, gtk.Label("liststore"))
        
        # build a table to put all my stuffs
        self.table2 = gtk.Table(100, 100, True)
        self.table2.show()
        self.frame2.add(self.table2)

        self.sw3 = gtk.ScrolledWindow()
        self.sw3.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        
        self.liststore = gtk.ListStore(str, int, float, float, int)
        self.treeview2 = gtk.TreeView(self.liststore)

        self.namecolumn = gtk.TreeViewColumn('Ticker')
        self.bidsizecolumn = gtk.TreeViewColumn('BidSize')
        self.bidpricecolumn = gtk.TreeViewColumn('BidPrice')
        self.askpricecolumn = gtk.TreeViewColumn('AskPrice')
        self.asksizecolumn = gtk.TreeViewColumn('AskSize')

        self.treeview2.append_column(self.namecolumn)
        self.treeview2.append_column(self.bidsizecolumn)
        self.treeview2.append_column(self.bidpricecolumn)
        self.treeview2.append_column(self.askpricecolumn)
        self.treeview2.append_column(self.asksizecolumn)

        self.namecell = gtk.CellRendererText()
        self.namecell.set_property( 'editable', True )
        self.namecell.connect( 'edited', self.col0_edited, self.liststore)
        self.namecolumn.pack_start(self.namecell, True)
        self.namecolumn.add_attribute(self.namecell, 'text', 0)

        self.bidsizecell = gtk.CellRendererText()
        self.bidsizecolumn.pack_start(self.bidsizecell, True)
        self.bidsizecolumn.add_attribute(self.bidsizecell, 'text', 1)

        self.bidpricecell = gtk.CellRendererText()
        self.bidpricecolumn.pack_start(self.bidpricecell, True)
        self.bidpricecolumn.add_attribute(self.bidpricecell, 'text', 2)

        self.askpricecell = gtk.CellRendererText()
        self.askpricecolumn.pack_start(self.askpricecell, True)
        self.askpricecolumn.add_attribute(self.askpricecell, 'text', 3)

        self.asksizecell = gtk.CellRendererText()
        self.asksizecolumn.pack_start(self.asksizecell, True)
        self.asksizecolumn.add_attribute(self.asksizecell, 'text', 4)

        self.treeview2.show()
        self.sw3.add(self.treeview2)
        self.sw3.show()
        self.table2.attach(self.sw3, 0, 100, 0, 100)
        
        self.name2iter = dict()
        
        self.name2iter["STAN"] = self.liststore.append(["STAN", 10, 1402.0, 1432.2, 100])
        self.name2iter["GS"] = self.liststore.append(["GS", 10, 1402.0, 1432.2, 100])

        self.sw3.connect("key_press_event", self.key_pressed2, None)
        
        #window.fullscreen()
        self.window.show()

    def col0_edited( self, cell, path, new_text, model ):
        print "Change '%s' to '%s'" % (model[path][0], new_text)
        model[path][0] = new_text
        return
 
    def key_pressed2(self, widget, event, data=None):
        if event.keyval == 65474:
            self.liststore.append()
 
def main():
    gtk.main()
    return 0

if __name__ == "__main__":
    MyNotebook()
    main()
