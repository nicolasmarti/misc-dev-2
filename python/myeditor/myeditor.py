#!/usr/bin/env python

import pygtk
pygtk.require('2.0')
import gtk
import sets

class MyBuffer(gtk.TextBuffer):

    def input_key(self, pressed_key):
        pass

    def __init__(self):
        
        gtk.TextBuffer.__init__(self)

        self.pressed_buffer = []


class MyView(gtk.TextView):

    def key_pressed(self, widget, event, data=None):
        self.pressed_key.add(event.keyval)
        print "pressed: " + str(self.pressed_key)


    def key_released(self, widget, event, data=None):
        self.pressed_key.remove(event.keyval)
        print "pressed: " + str(self.pressed_key)

    def __init__(self, buffer):
        
        gtk.TextView.__init__(self, buffer)

        # not editable: we grab things ... 
        self.set_editable(False)

        # the set of pressed keys
        self.pressed_key = sets.Set()

        # the key handlers
        self.connect("key_press_event", self.key_pressed, None)
        self.connect("key_release_event", self.key_released, None)

        


class MyEditor:
    
    def close_application(self, widget):
        gtk.main_quit()

    def __init__(self):
        
        window = gtk.Window(gtk.WINDOW_TOPLEVEL)
        window.set_resizable(True)  
        window.connect("destroy", self.close_application)
        window.set_title("TextView Widget Basic Example")
        window.set_border_width(0)

        sw = gtk.ScrolledWindow()
        sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        textbuffer = MyBuffer()
        textview = MyView(textbuffer)
        
        sw.add(textview)
        sw.show()
        textview.show()

        window.add(sw)
        sw.show()

        window.resize(800, 600)

        window.show()

def main():
    gtk.main()
    return 0       

if __name__ == "__main__":
    MyEditor()
    main()

