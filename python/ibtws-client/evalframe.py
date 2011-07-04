import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from threading import *

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
