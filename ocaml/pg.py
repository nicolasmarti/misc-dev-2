import os, os.path
import sys
import pygtk
pygtk.require ('2.0')

import gtk
if gtk.pygtk_version < (2,10,0):
    print "PyGtk 2.10 or later required for this example"
    raise SystemExit

import gtksourceview2
import pango

from sets import *
import keybinding

class PG(gtksourceview2.View, keybinding.KeyBinding):
    
    def __init__(self):

        # first define a buffer and its language manager
        lm = gtksourceview2.LanguageManager()
        self.buffer = gtksourceview2.Buffer()
        self.buffer.set_data('languages-manager', lm)

        # initialize super class using the buffer
        gtksourceview2.View.__init__(self, self.buffer)

        # attach key callback
        self.connect("key_press_event", self.key_pressed, None)
        self.connect("key_release_event", self.key_released, None)

        # initialize super class keybing
        keybinding.KeyBinding.__init__(self)
        self.ctrl = 65507

        # a simple keybinding for test
        # C-x C-c -> close the application
        self.keyactions.append(
            ([Set([65507, 120]), Set([65507,99])],
             lambda s: gtk.main_quit()
             )
            )

        # C-c C-n -> proceed next
        self.keyactions.append(
            ([Set([65507, 99]), Set([65507,110])],
             lambda s: s.proceed_definition()
             )
            )

        # C-c C-u -> undo last definition
        self.keyactions.append(
            ([Set([65507, 99]), Set([65507,117])],
             lambda s: s.undo()
             )
            )

    # remove all marks
    def remove_all_marks(self):
        begin, end = self.buffer.get_bounds()
        self.buffer.remove_source_marks(begin, end)

    # key callback
    def key_pressed(self, widget, event, data=None):        
        self.keypressed(event.keyval)
        if event.state & gtk.gdk.CONTROL_MASK: self.keypressed(self.ctrl)
        #print event.keyval
        return

    def key_released(self, widget, event, data=None):        
        self.keyreleased(event.keyval)
        if not (event.state & gtk.gdk.CONTROL_MASK): self.keyreleased(self.ctrl)
        return

    # proceed next definition
    def proceed_definition(self):
        print "proceed_definition"
        return

    # undo last definition
    def undo(self):
        print "undo"
        return


if __name__ == '__main__':
    
    srcview = PG()

    win = gtk.Window()
    win.add(srcview)

    win.connect('destroy', lambda win: gtk.main_quit())

    win.resize(800, 600)

    win.show_all()

    gtk.main()
