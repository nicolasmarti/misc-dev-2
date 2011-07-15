"""
a first temptative to build a graphical sheet in gtk using TreeView
"""

import pygtk
pygtk.require('2.0')
import gtk
from gtk import gdk
import re
from string import join, ascii_uppercase

from spreadsheet import *

def colnum2colname(n):
    
    res = ""

    if n / 26 > 0:
        res += colnum2colname (n / 26 - 1)
        
    res += ascii_uppercase[n%26]

    return res

def colname2colnum(s):
    
    res = 0
    for i in s:
        res *= 26
        res += ord(i) - ord('A') + 1

    return res

class CellRender(gtk.CellRendererText):

    def __init__(self, col, store, ss):

        gtk.CellRendererText.__init__(self)

        self.connect('editing-started', self.editing_start)
        self.connect('editing-canceled', self.editing_cancel)

        self.store = store
        self.ss = ss

        self.ss._debug = False

        self.col = col

    def editing_start(self, cell, editable, path, user_param = None):
        print "editing_start"
        try:
            f = self.ss.getformula(colnum2colname(self.col - 1) + str(int(path) + 1))
            editable.set_text(f)
        except:
            pass

    def editing_cancel(self, cell, user_param = None):
        print "editing_cancel"


class Sheet(gtk.TreeView):

    def __init__(self, numCols = 100, numRows = 100):

        gtk.TreeView.__init__(self)

        # the underlying ss
        self.ss = SpreadSheet(callback = self.setcell)

        # numbers of row / columns
        self.numCols = numCols
        self.numRows = numRows

        # build the storage of data
        types =  [str]*(self.numCols+1)
        self.store = gtk.ListStore(*types)

        # fill it with empty stuffs
        for i in range(self.numRows):
            self.store.append([str(i+1)] + [""] * self.numCols)

        # add columns
        for i in range(self.numCols + 1):
            cellrenderertext = CellRender(i, self.store, self.ss)

            cellrenderertext.connect('edited', self.edited_cb, i)

            if i > 0:
                cellrenderertext.set_property('editable', True)

            column = gtk.TreeViewColumn('%s'% colnum2colname(i - 1) if (i > 0) else "", cellrenderertext, text=i)
            
            column.set_sizing(gtk.TREE_VIEW_COLUMN_AUTOSIZE)

            column.set_min_width(100)

            if i == 0:
                self.firstcolumn = column

            self.append_column(column)

        

        self.set_rules_hint(True)

        self.set_model(self.store)

        self.connect("key_press_event", self.key_pressed, None)
        self.connect("row-activated", self.raw_activated, None)

        self.set_enable_search(False)

        #self.set_property('enable-grid-lines', True)
        
        self.set_grid_lines(gtk.TREE_VIEW_GRID_LINES_BOTH)

    def raw_activated(self, treeview, path, view_column, user_param1 = None):
        print "raw_activated"
        

    def key_pressed(self, widget, event, data=None):        
        # "=" ==> edit the cell        
        cursor = self.get_cursor()
        row = cursor[0][0]
        renders = cursor[1].get_cell_renderers()
        col = renders[0].col

        #self.set_cursor(str(row), cursor[1])
        #print event.keyval

        title = str((row, col))
        if col > 0:
            

        self.firstcolumn.set_title(title)
        

        # '='
        if event.keyval == 61:
            print (row, col)
            #renders[0].start_editing(event, self, str(row), self.get_visible_rect(), self.get_visible_rect(), gtk.CELL_RENDERER_INSENSITIVE)

        # Delete
        if event.keyval == 65535:
            key = colnum2colname(col - 1) + str(row + 1)
            self.ss.remove_key(key)
            print self.ss

        # Esc 
        if event.keyval == 65307:
            gtk.main_quit()

        # F2 -> save
        if event.keyval == 65471:
            self.filew = gtk.FileSelection("File selection")

            def close(w):
                self.filew.hide()

            def fileok(w):
                self.filew.hide()                
                self.ss.save(open(self.filew.get_filename(), 'wb'))
            
            self.filew.connect("destroy", close)
            self.filew.ok_button.connect("clicked", fileok)

            self.filew.show()

        # F3 -> load
        if event.keyval == 65472:
            self.filew = gtk.FileSelection("File selection")

            def close(w):
                self.filew.hide()

            def fileok(w):
                self.filew.hide()                
                self.ss.load(open(self.filew.get_filename(), 'rb'))
            
            self.filew.connect("destroy", close)
            self.filew.ok_button.connect("clicked", fileok)

            self.filew.show()


    def edited_cb(self, cell, path, new_text, user_data = None):
        #print "cell := " + str(cell)
        #print "path := " + str(path)
        #print "model[path][user_data] := " + str(self.store[path][user_data])
        #print "new_text := " + new_text
        #print "user_data := " + str(user_data) +"\n"

        try:
            if new_text[0] == '=':
                self.ss[colnum2colname(user_data - 1) + str(int(path) + 1)] = new_text
            else:
                self.ss[colnum2colname(user_data - 1) + str(int(path) + 1)] = eval(new_text)
        except:
            self.ss[colnum2colname(user_data - 1) + str(int(path) + 1)] = new_text

        #print self.ss
        #self.store[path][user_data] = new_text
        
    def setcell(self, action, param):
        if action == "update":
            key = param[0]
            value = param[1]
            print "ss callback: " + str((key, value))
            findcol = re.findall("[A-Z]+?", key)
            col = colname2colnum(join(findcol, ""))
            
            findrow = re.findall("(\d|\.)+?", key)
            row = int(join(findrow, ""))

            print str((col, row)) + " := " + str(value)
            
            self.store[row - 1][col] = str(value)
            return

        if action == "delete":
            key = param
            findcol = re.findall("[A-Z]+?", key)
            col = colname2colnum(join(findcol, ""))
            
            findrow = re.findall("(\d|\.)+?", key)
            row = int(join(findrow, ""))
            self.store[row - 1][col] = ""
            

if __name__ == '__main__':
    
    sw = gtk.ScrolledWindow()
    sw.set_shadow_type(gtk.SHADOW_ETCHED_IN)
    sw.set_policy(gtk.POLICY_AUTOMATIC,
                  gtk.POLICY_AUTOMATIC)

    sheet = Sheet()
    sw.add(sheet)
    win = gtk.Window()
    win.add(sw)

    win.connect('destroy', lambda win: gtk.main_quit())

    win.resize(800, 600)

    win.show_all()

    gtk.main()
