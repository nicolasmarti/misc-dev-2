#!/usr/bin/env python

import pygtk
pygtk.require('2.0')
import gtk
from sets import *
from types import *
import random

class MyBuffer(gtk.TextBuffer):

    def managekey(self, s):
        pass

    def __init__(self):
        
        gtk.TextBuffer.__init__(self)

        #self.set_text(str(random.random()*100))
        
# :: [(list (set int), void (MyView))]
keysemantics = [
    ([Set([65507, 120]), Set([48])],
     lambda mv: mv.myframe.undivide()
     ),
    ([Set([65507, 120]), Set([50])],
     lambda mv: mv.myframe.divideV()
     ),
    ([Set([65507, 120]), Set([51])],
     lambda mv: mv.myframe.divideH()
     ),
    ([Set([65507, 120]), Set([65507, 99])],
     lambda mv: gtk.main_quit()
     ),
    ([Set([65507, 120]), Set([111])],
     lambda mv: mv.myframe.focusnext()
     )
    ]

# the currently focused buffer
is_focus = None

#the main window
mainwin = None

#the set of buffer
bufferset = Set()

class MyView(gtk.TextView):

    def managekey(self):
        global mainwin

        valid = False
        for i in keysemantics:
            if len(i[0]) > len(self.validkeysequences):
                prefix = True
                for j in range(0, len(self.validkeysequences) - 1):
                    prefix = prefix and (self.validkeysequences[j] == i[0][j])
                    
                if prefix:
                    if self.pressed_key == i[0][len(self.validkeysequences)]:
                        self.validkeysequences.append(self.pressed_key)
                        if len(self.validkeysequences) == len(i[0]):
                            self.validkeysequences = []
                            self.pressed_key = Set()
                            i[1](self)
                            return
                        else:
                            valid = True
                    elif self.pressed_key <= i[0][len(self.validkeysequences)] and (len(self.validkeysequences) > 0 or Set([65507]) <= self.pressed_key):
                        valid = True

        #print "valid = " + str(valid)
        #print "self.validkeysequences = " + str(self.validkeysequences)

        if valid:
            self.set_editable(False)
            mainwin.set_title(str(self.validkeysequences))
            return

        if not valid and len(self.validkeysequences) > 0:
            self.set_editable(False)
            self.validkeysequences = []
            mainwin.set_title("unknown key sequence")
            return
        
        if not valid:
            self.get_buffer().managekey(self.pressed_key)                
            self.validkeysequences = []
            self.set_editable(True)
            return

    def key_pressed(self, widget, event, data=None):        
        global mainwin
        self.pressed_key.add(event.keyval)
        self.managekey()
        #print "pressed: " + str(self.pressed_key)


    def key_released(self, widget, event, data=None):
        self.pressed_key.discard(event.keyval)

    def get_focus(self, widget, event, data=None):
        global is_focus
        global mainwin
        is_focus = self
        mainwin.set_title(str(self.validkeysequences))

    def __init__(self, buffer):
        
        gtk.TextView.__init__(self, buffer)

        # not editable: we grab things ... 
        self.set_editable(True)

        # the set of pressed keys
        self.pressed_key = Set()

        # the key handlers
        self.connect("key_press_event", self.key_pressed, None)
        self.connect("key_release_event", self.key_released, None)
        self.connect("focus-in-event", self.get_focus, None)

        self.show()

        # :: [Set (int)]
        self.validkeysequences = []

        self.get_settings().set_property("gtk-error-bell", False)
        

class MyFrame(gtk.Frame):
    
    def getTextBuffer(self):

        if self.mode == "PLAIN":
            return self.inside.get_buffer()
        
        if self.mode == "SPLITTED":
            return self.inside.get_child1().getTextBuffer()

    def getTextView(self):

        if self.mode == "PLAIN":
            return self.inside
        
        if self.mode == "SPLITTED":
            return self.inside.get_child1().getTextView()

    def isChild(self, textview):
        if self.mode == "PLAIN":
            return self.inside == textview

        if self.mode == "SPLITTED":
            return self.inside.get_child1().isChild(textview) or self.inside.get_child2().isChild(textview)

    def divideH(self):

        textbuf = self.getTextBuffer()
        #textbuf = MyBuffer()

        self.remove(self.inside)

        child1 = MyFrame(self.inside, self.mode)
        child1.myframe = self

        child2 = MyFrame(MyView(textbuf))
        child2.myframe = self

        panel = gtk.HPaned()

        panel.pack1(child1, False, False)
        panel.pack2(child2, False, False)
        panel.show()
        
        self.add(panel)
        self.inside = panel
        self.mode = "SPLITTED"

        child1.getTextView().grab_focus()

    def divideV(self):

        textbuf = self.getTextBuffer()
        #textbuf = MyBuffer()

        self.remove(self.inside)

        child1 = MyFrame(self.inside, self.mode)
        child1.myframe = self

        child2 = MyFrame(MyView(textbuf))
        child2.myframe = self

        panel = gtk.VPaned()

        panel.pack1(child1, False, False)
        panel.pack2(child2, False, False)
        panel.show()
        
        self.add(panel)
        self.inside = panel
        self.mode = "SPLITTED"

        child1.getTextView().grab_focus()

    def setMyFrame(self, frame):
        if self.mode == "SPLITTED":
            child1 = self.inside.get_child1()
            child1.myframe = frame

            child2 = self.inside.get_child2()
            child2.myframe = frame

            return

        if self.mode == "PLAIN":
            self.myframe = frame

    def undivide(self):

        if self.mode == "SPLITTED":
            child1 = self.inside.get_child1()
            child1.setMyFrame(self)

            child2 = self.inside.get_child2()
            child2.setMyFrame(self)
            
            self.inside.remove(child1)
            self.inside.remove(child2)

            child1.remove(child1.inside)
            child2.remove(child2.inside)

            if child2.isChild(is_focus):

                self.remove(self.inside)
                self.inside = child1.inside
                child1.inside.myframe = self
                self.add(child1.inside)
                self.mode = child1.mode

                child1.getTextView().grab_focus()
                return

            if child1.isChild(is_focus):

                self.remove(self.inside)
                self.inside = child2.inside
                child2.inside.myframe = self
                self.add(child2.inside)
                self.mode = child2.mode

                child2.getTextView().grab_focus()
                return


        if self.mode == "PLAIN" and self.myframe <> self:
            self.myframe.undivide()

    def tostring(self):
        if self.mode == "PLAIN":

            if self.inside.myframe <> self:
                raise Exception('child wrong !!!')

            return "(" + str(self) + ")"
            
        if self.mode == "SPLITTED":
            child1 = self.inside.get_child1()

            if child1.myframe <> self:
                raise Exception('left child wrong !!!')

            child2 = self.inside.get_child2()

            if child2.myframe <> self:
                raise Exception('left child wrong !!!')

            return child1.tostring() + " <--(" + str(self) + ")--> " + child2.tostring()

    def focusnext(self):
        global is_focus

        if self.mode == "PLAIN":
            if self.myframe == self:
                #print "prout1"
                self.getTextView().grab_focus()
                return
            else:
                #print "prout2"
                self.myframe.focusnext()
                return   

        if self.mode == "SPLITTED":
            child1 = self.inside.get_child1()
            child2 = self.inside.get_child2()

            if child1.isChild(is_focus):
                #print "prout3"
                child2.getTextView().grab_focus()
                return
            else:
                if self.myframe == self:
                    #print "prout4"
                    self.getTextView().grab_focus()
                    return
                else:
                    #print "prout5"
                    self.myframe.focusnext()
                    return   


    def __init__(self, inside, mode = "PLAIN"):

        gtk.Frame.__init__(self)
        self.inside = inside        
        self.add(inside)
        self.show()

        self.mode = mode

        if mode == "PLAIN":
            self.inside.myframe = self

        self.myframe = self

        


class MyEditor:
    
    def close_application(self, widget):
        gtk.main_quit()

    def __init__(self):
        
        global mainwin
        global bufferset

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

        mainwin = window
        bufferset.add(textbuffer)


        #mainFrame.divideH()
        #mainFrame.divideV()

        #mainFrame.undivide()
        #mainFrame.undivide()

        window.resize(800, 600)

        window.show()

        #def printmainframe(frame):
        #    print frame.tostring()

        #keysemantics.append( 
        #    ([Set([65507, 120]), Set([113])],
        #     lambda mv: printmainframe(mainFrame)
        #     )
        #    )

def main():
    gtk.main()
    return 0       

if __name__ == "__main__":
    MyEditor()
    main()

