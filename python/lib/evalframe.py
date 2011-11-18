import pygtk
pygtk.require('2.0')
import gobject 
import gtk

from threading import *
import keybinding

from sets import *

import spreadsheet

class EvalFrame(gtk.Frame, Thread, keybinding.KeyBinding):
    
    def __init__(self, _locals = None):
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
        self.button = gtk.Button(label="execute(C-c C-c)")
        self.button.show()
        self.table.attach(self.button, 3, 6, 8, 9)
        self.button.connect("clicked", self.myexec, None)

        self.button = gtk.Button(label="eval(C-c C-n)")
        self.button.show()
        self.table.attach(self.button, 0, 3, 8, 9)
        self.button.connect("clicked", self.myeval, None)

        self.button = gtk.Button(label="???")
        self.button.show()
        self.table.attach(self.button, 6, 10, 8, 9)

        if _locals == None:
            self.m_locals = locals()
        else:
            self.m_locals = _locals

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

        for i in [self, self.textview]:
            i.connect("key_press_event", self.key_pressed, None)
            i.connect("key_release_event", self.key_released, None)
        


        # initialize super class keybing
        keybinding.KeyBinding.__init__(self)
        self.ctrl = 65507

        # C-x C-c -> close the application
        self.keyactions.append(
            ([Set([65507, 120]), Set([65507,99])],
             lambda s: gtk.main_quit()
             )
            )

        # C-c C-c -> execute
        self.keyactions.append(
            ([Set([65507, 99]), Set([65507,99])],
             lambda s: self.myexec()
             )
            )

        # C-c C-c -> eval
        self.keyactions.append(
            ([Set([65507, 99]), Set([65507,110])],
             lambda s: self.myeval()
             )
            )

        # this is a historic of the commands
        self.hist = []
        # and a pointer
        self.histn = None
        # and a buffer for the current command
        self.savedcmd = None

        # C-up -> get the previous command
        self.keyactions.append(
            ([Set([65507, 65362])],
             lambda s: self.hist_previous()
             )
            )

        # C-down -> get the next command
        self.keyactions.append(
            ([Set([65507, 65364])],
             lambda s: self.hist_next()
             )
            )

        self.get_settings().set_property("gtk-error-bell", False)

        try:
            exec "import Doudou" in globals()
        except:
            None

    # key callback
    def key_pressed(self, widget, event, data=None):        
        self.keypressed(event.keyval)
        if event.state & gtk.gdk.CONTROL_MASK: self.keypressed(self.ctrl)
        #print event.keyval
        self.textview.grab_focus()
        return

    def key_released(self, widget, event, data=None):        
        self.keyreleased(event.keyval)
        if not (event.state & gtk.gdk.CONTROL_MASK): self.keyreleased(self.ctrl)
        self.textview.grab_focus()
        return


    def myexec(self, data=None):
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
                
        self.hist.append(m_str)
        self.histn = None

        self.textview.grab_focus()

    def myeval(self, data=None):
        m_str = self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())
        try:

            self.textbuffer2.set_text(str(eval(m_str, globals(), self.m_locals)))        
            self.m_start = self.textbuffer.get_end_iter()
            self.textbuffer.set_text("")

        except BaseException as e:
            self.textbuffer2.set_text(str(e))        

            self.textview.grab_focus()

        self.hist.append(m_str)
        self.histn = None

    def local_clicked(self, treeview, path, viewcolumn, data):
        #print "treeview: " + str(treeview) + " :: " + str(type(treeview))
        #print "path: " + str(path) + " :: " + str(type(path))
        #print "viewcolumn: " + str(viewcolumn) + " :: " + str(type(viewcolumn))
        #print "data: " + str(data) + " :: " + str(type(data))

        piter = treeview.get_model().get_iter(path)
        varname = str(treeview.get_model().get_value(piter, 0))
        self.textbuffer.insert(self.textbuffer.get_end_iter(), varname)
        self.textview.grab_focus()

    def hist_previous(self):

        # first time we look for the historic, or if the pointer is on the length of the hist, we need to save the current command
        if self.histn == None or self.histn == len(self.hist):
            self.savedcmd = self.textbuffer.get_text(self.textbuffer.get_start_iter(), self.textbuffer.get_end_iter())

        # first set up the pointer
        if self.histn == None:
            self.histn = len(self.hist) - 1
        else:
            self.histn -= 1

        # make sure we are at least at 0
        if self.histn < 0:
            self.histn = 0

        # and make sure it points to something
        if self.histn >= len(self.hist):
            self.hist = None
            return


        # change the current value of the buffer with the historical command
        self.textbuffer.set_text(self.hist[self.histn])
        return
        
    def hist_next(self):
        # if the pointer is not set, do nothing
        if self.histn == None: return

        # else update it
        self.histn += 1

        # if it is gt to the length of the historic, then we assign to the length, and show the current command
        if self.histn >= len(self.hist): 
            self.histn = len(self.hist)
            self.textbuffer.set_text(self.savedcmd)
        else:
            self.textbuffer.set_text(self.hist[self.histn])
        
        return

if __name__ == '__main__':
    
    sw = gtk.ScrolledWindow()
    sw.set_shadow_type(gtk.SHADOW_ETCHED_IN)
    sw.set_policy(gtk.POLICY_AUTOMATIC,
                  gtk.POLICY_AUTOMATIC)

    ss = spreadsheet.SpreadSheet(_globals = globals())
    evalf = EvalFrame(ss)
    sw.add(evalf)
    win = gtk.Window()
    win.add(sw)

    win.connect('destroy', lambda win: gtk.main_quit())

    win.resize(800, 600)

    win.show_all()

    gtk.main()
