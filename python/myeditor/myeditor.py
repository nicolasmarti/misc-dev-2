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
        print str(self) + "pressed: " + str(self.pressed_key)


    def key_released(self, widget, event, data=None):
        self.pressed_key.remove(event.keyval)
        print str(self) + "pressed: " + str(self.pressed_key)

    def __init__(self, buffer):
        
        gtk.TextView.__init__(self, buffer)

        # not editable: we grab things ... 
        self.set_editable(False)

        # the set of pressed keys
        self.pressed_key = sets.Set()

        # the key handlers
        self.connect("key_press_event", self.key_pressed, None)
        self.connect("key_release_event", self.key_released, None)

        self.show()

        buffer.set_text("doudou")



class MyFrame(gtk.Frame):
    
    def getTextBuffer(self):

        if self.mode == "PLAIN":
            return self.inside.get_buffer()
        
        if self.mode == "SPLITTED":
            return self.inside.get_child1().getTextBuffer()

    def divideH(self):

        textbuf = self.getTextBuffer()

        self.remove(self.inside)

        child1 = MyFrame(self.inside, self.mode)
        child2 = MyFrame(MyView(textbuf))

        panel = gtk.HPaned()

        panel.pack1(child1, False, False)
        panel.pack2(child2, False, False)
        panel.show()
        
        self.add(panel)
        self.inside = panel
        self.mode = "SPLITTED"

    def divideV(self):

        textbuf = self.getTextBuffer()

        self.remove(self.inside)

        child1 = MyFrame(self.inside, self.mode)
        child2 = MyFrame(MyView(textbuf))

        panel = gtk.VPaned()

        panel.pack1(child1, False, False)
        panel.pack2(child2, False, False)
        panel.show()
        
        self.add(panel)
        self.inside = panel
        self.mode = "SPLITTED"

    def undivide(self):

        if self.mode == "SPLITTED":
            child1 = self.inside.get_child1()
            child2 = self.inside.get_child2()
            
            self.inside.remove(child1)
            self.inside.remove(child2)

            child1.remove(child1.inside)
            self.remove(self.inside)

            self.inside = child1.inside
            self.add(child1.inside)
            self.mode = child1.mode

    def __init__(self, inside, mode = "PLAIN"):

        gtk.Frame.__init__(self)
        self.inside = inside        
        self.add(inside)
        self.show()

        self.mode = mode


class MyEditor:
    
    def close_application(self, widget):
        gtk.main_quit()

    def __init__(self):
        
        window = gtk.Window(gtk.WINDOW_TOPLEVEL)
        window.set_resizable(True)  
        window.connect("destroy", self.close_application)
        window.set_title("TextView Widget Basic Example")
        window.set_border_width(0)

        #sw = gtk.ScrolledWindow()
        #sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)

        textbuffer = MyBuffer()
        textview = MyView(textbuffer)
        mainFrame = MyFrame(textview)
        
        window.add(mainFrame)
        
        mainFrame.divideH()
        mainFrame.divideV()

        #mainFrame.undivide()
        #mainFrame.undivide()

        window.resize(800, 600)

        window.show()

def main():
    gtk.main()
    return 0       

if __name__ == "__main__":
    MyEditor()
    main()

