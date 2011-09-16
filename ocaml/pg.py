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

        # the current starting position for position
        self.startpos = [0]

        # a tag for uneditable text 
        self.not_editable_tag = self.buffer.create_tag(editable=False, foreground="purple", background="green")

        # modifying theme for sake of readability
        self.modify_base(gtk.STATE_NORMAL, gtk.gdk.color_parse('black'))
        self.modify_text(gtk.STATE_NORMAL, gtk.gdk.color_parse('white'))


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
        # grab the start iterator
        startpos = self.startpos[len(self.startpos) - 1]
        startiter = self.buffer.get_iter_at_offset(startpos)
        # grab the last iter of the buffer
        enditer = self.buffer.get_end_iter()
        # grab the text
        text = self.buffer.get_text(startiter, enditer)
        # proceed the term
        endpos, res = Doudou.proceed(text)
        # update starting position
        endpos = startpos + endpos
        self.startpos.append(endpos)

        enditer = self.buffer.get_iter_at_offset(endpos)

        # create a texttag

        self.buffer.apply_tag(self.not_editable_tag, startiter, enditer)
        
        #print self.startpos
        return

    # undo last definition
    def undo(self):
        if len(self.startpos) == 1: return
        # calling the undo
        Doudou.undo()
        # poping the last starting position
        oldendpos = self.startpos.pop()

        # removing the tag
        newendpos = self.startpos[len(self.startpos) - 1]

        oldenditer = self.buffer.get_iter_at_offset(oldendpos)
        newenditer = self.buffer.get_iter_at_offset(newendpos)

        self.buffer.remove_tag(self.not_editable_tag, newenditer, oldenditer)

        #print self.startpos
        
        return


if __name__ == '__main__':
    
    srcview = PG()

    win = gtk.Window()
    win.add(srcview)

    win.connect('destroy', lambda win: gtk.main_quit())

    win.resize(800, 600)

    win.show_all()

    gtk.main()
