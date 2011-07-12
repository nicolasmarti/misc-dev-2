#!/usr/bin/env python

import pygtk
pygtk.require('2.0')
import gtk
from sets import *
from types import *
import random
from time import *

# the global dictionnary used
state = dict()

class MyBuffer(gtk.TextBuffer):

    def managekey(self, s):
        state["myentry"].set_text("")
        pass

    def attach(self, textview):
        pass

    def __init__(self, name):
        
        global state

        gtk.TextBuffer.__init__(self)
        
        state["buffers"].append(self)

        self.name = name
        #self.set_text(str(random.random()*100))

def newbuffer(mv):
    mv.set_buffer(MyBuffer(str(random.random())))
    mv.grab_focus()

def switchbuffer(mv):
    global state
    root = mv.myframe.get_root()
    
    for i in range(0, len(state["buffers"])):
        if not root.isChildBuffer(state["buffers"][i]):
            buffer = state["buffers"].pop(i)
            state["buffers"].append(buffer)
            mv.set_buffer(buffer)
            mv.grab_focus()
            return
    mv.grab_focus()

def askswitchbuffer(mv):
    global state
    state["myentry"].set_text("NYI")

def openfile(mv):
    global state

    def action(txt):
        state["myentry"].set_text("NYI: open file " + txt)
        mv.grab_focus()
        return None

    state["myentry"].setquestion("file: ", action)
    
    


# list of key bindings
state["keysemantics"] = [
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
     ),
    ([Set([65507, 120]), Set([110])],
     lambda mv: newbuffer(mv)
     ),
    ([Set([65507, 120]), Set([98])],
     lambda mv: switchbuffer(mv)
     ),
    ([Set([65507, 120]), Set([65507, 98])],
     lambda mv: askswitchbuffer(mv)
     ),
    ([Set([65507, 120]), Set([65507, 102])],
     lambda mv: openfile(mv)
     )
    ]

# the currently focused buffer
state["is_focus"] = None

#the main window
state["mainwin"] = None

#the set of buffer
# a dictionnary from names to buffer
state["buffers"] = []

# parameters for building Hspan
state["resize"] = False
state["shrink"] = False

def list_set_key_val2string(ls):
    sl = []
    for i in ls:
        ssl = []
        for j in i:
            ssl.append(gtk.gdk.keyval_name(j))
        sl.append(ssl)

    res = ""
    for i in sl:
        for j in reversed(range(0,len(i))):
            if j <> len(i) - 1:
                res += "-"
            res += i[j]
        res += ""
        
    return res
            

class MyView(gtk.TextView):

    def set_buffer(self, buffer):
        buffer.attach(self)
        gtk.TextView.set_buffer(self, buffer)

    def managekey(self):
        global state

        valid = False
        for i in state["keysemantics"]:
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
                            self.set_editable(False)                            
                            self.grab_focus()
                            state["mainwin"].set_title(self.get_buffer().name + " " + list_set_key_val2string(self.validkeysequences))
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
            state["mainwin"].set_title(self.get_buffer().name + " " + list_set_key_val2string(self.validkeysequences))
            self.grab_focus()
            return

        if not valid and len(self.validkeysequences) > 0:
            self.set_editable(False)
            self.validkeysequences = []
            self.grab_focus()
            state["mainwin"].set_title(self.get_buffer().name + " Unknown sequence")
            return
        
        if not valid:
            self.get_buffer().managekey(self.pressed_key)                
            self.validkeysequences = []
            self.set_editable(True)
            return

    def key_pressed(self, widget, event, data=None):        
        self.pressed_key.add(event.keyval)
        print event.keyval
        self.managekey()

    def key_released(self, widget, event, data=None):
        self.pressed_key.discard(event.keyval)

    def get_focus(self, widget, event, data=None):
        global state
        self.validkeysequences = []
        self.pressed_key = Set()
        state["is_focus"] = self
        state["mainwin"].set_title(self.get_buffer().name + " " + list_set_key_val2string(self.validkeysequences))

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

        self.set_wrap_mode(gtk.WRAP_NONE)

        if buffer <> None:
            buffer.attach(self)

        self.modify_base(gtk.STATE_NORMAL, gtk.gdk.color_parse('black'))
        self.modify_text(gtk.STATE_NORMAL, gtk.gdk.color_parse('white'))
        
        return



class MyFrame(gtk.Frame):

    def getTextBuffer(self):

        if self.mode == "PLAIN":
            return self.inside.get_child().get_buffer()
        
        if self.mode == "SPLITTED":
            return self.inside.get_child1().getTextBuffer()

    def getTextView(self):

        if self.mode == "PLAIN":
            return self.inside.get_child()
        
        if self.mode == "SPLITTED":
            return self.inside.get_child1().getTextView()

    def isChildView(self, textview):
        if self.mode == "PLAIN":
            return self.inside.get_child() == textview

        if self.mode == "SPLITTED":
            return self.inside.get_child1().isChildView(textview) or self.inside.get_child2().isChildView(textview)

    def isChildBuffer(self, textbuffer):
        if self.mode == "PLAIN":
            return self.inside.get_child().get_buffer() == textbuffer

        if self.mode == "SPLITTED":
            return self.inside.get_child1().isChildBuffer(textbuffer) or self.inside.get_child2().isChildBuffer(textbuffer)

    def divideH(self):

        global state

        textbuf = self.getTextBuffer()
        #textbuf = MyBuffer()

        self.remove(self.inside)

        child1 = MyFrame(self.inside, self.mode)
        child1.myframe = self

        sw = gtk.ScrolledWindow()
        sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        sw.add(MyView(textbuf))
        sw.show()

        child2 = MyFrame(sw)
        child2.myframe = self

        panel = gtk.HPaned()

        panel.pack1(child1, state["resize"], state["shrink"])
        panel.pack2(child2, state["resize"], state["shrink"])
        panel.show()
        
        self.add(panel)
        self.inside = panel
        self.mode = "SPLITTED"

        child1.getTextView().grab_focus()

    def divideV(self):

        global state

        textbuf = self.getTextBuffer()
        #textbuf = MyBuffer()

        self.remove(self.inside)

        child1 = MyFrame(self.inside, self.mode)
        child1.myframe = self

        sw = gtk.ScrolledWindow()
        sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        sw.add(MyView(textbuf))
        sw.show()

        child2 = MyFrame(sw)
        child2.myframe = self

        panel = gtk.VPaned()

        panel.pack1(child1, state["resize"], state["shrink"])
        panel.pack2(child2, state["resize"], state["shrink"])
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
            self.inside.get_child().myframe = frame

    def undivide(self):
        
        print "undivide: " + str(self)

        global state

        if self.mode == "SPLITTED":

            child1 = self.inside.get_child1()
            child1.setMyFrame(self)

            child2 = self.inside.get_child2()
            child2.setMyFrame(self)
            
            self.inside.remove(child1)
            self.inside.remove(child2)

            child1.remove(child1.inside)
            child2.remove(child2.inside)

            if child2.isChildView(state["is_focus"]):

                self.remove(self.inside)
                self.inside = child1.inside
                self.add(child1.inside)
                self.mode = child1.mode

                child1.getTextView().grab_focus()
                return

            if child1.isChildView(state["is_focus"]):

                self.remove(self.inside)
                self.inside = child2.inside
                self.add(child2.inside)
                self.mode = child2.mode

                child2.getTextView().grab_focus()
                return


        if self.mode == "PLAIN" and self.myframe <> self:
            self.myframe.undivide()

        

    def tostring(self):
        if self.mode == "PLAIN":

            if self.inside.get_child().myframe <> self:
                raise Exception('child wrong !!!')

            return "(" + str(self) + ")"
            
        if self.mode == "SPLITTED":
            child1 = self.inside.get_child1()

            if child1.myframe <> self:
                raise Exception('left child wrong !!!')

            child2 = self.inside.get_child2()

            if child2.myframe <> self:
                raise Exception('left child wrong !!!')

            return "( " + child1.tostring() + " <--(" + str(self) + ")--> " + child2.tostring() + " )"

    def focusnext(self):
        global state

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

            if child1.isChildView(state["is_focus"]):
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


    def get_root(self):
        if self.myframe == self:
            return self
        else:
            return self.myframe.get_root()        

    def __init__(self, inside, mode = "PLAIN"):

        gtk.Frame.__init__(self)

        self.inside = inside        
        self.add(inside)
        self.show()

        self.mode = mode

        if mode == "PLAIN":
            self.inside.get_child().myframe = self

        self.myframe = self
    
state["myentry"] = None
    
class MyEntry(gtk.Entry):

    def key_pressed(self, widget, event, data=None):        
        print event.keyval
        if (event.keyval == 65293):
            text = self.get_text()
            self.set_text("")
            self.disconnect(self.keypressedid)
            self.set_editable(False)
            self.set_can_focus(False)
            action = self.on_enter
            action(text)


    def __init__(self):

        gtk.Entry.__init__(self)

        self.on_enter = None

        self.set_editable(False)

        self.modify_base(gtk.STATE_NORMAL, gtk.gdk.color_parse('black'))
        
        self.set_can_focus(False)

    def setquestion(self, text, action):
        self.on_enter = action
        self.set_editable(True)
        self.set_text(text)
        self.keypressedid = self.connect("key_press_event", self.key_pressed, None)
        self.set_can_focus(True)
        self.grab_focus()


class MyEditor:
    
    def close_application(self, widget):
        gtk.main_quit()

    def __init__(self):
        
        global state

        window = gtk.Window(gtk.WINDOW_TOPLEVEL)
        window.set_resizable(True)  
        window.connect("destroy", self.close_application)
        window.set_title("TextView Widget Basic Example")
        window.set_border_width(0)

        textbuffer = MyBuffer("init")
        textview = MyView(textbuffer)

        sw = gtk.ScrolledWindow()
        sw.set_policy(gtk.POLICY_AUTOMATIC, gtk.POLICY_AUTOMATIC)
        sw.add(textview)

        sw.show()

        mainFrame = MyFrame(sw)

        entry = MyEntry()
        entry.set_editable(False)        
        state["myentry"] = entry
        entry.show()

        root_layout = gtk.VPaned()
        root_layout.pack1(mainFrame, True, True)
        root_layout.pack2(entry, False, True)
        root_layout.show()        

        window.add(root_layout)
        #window.add(mainFrame)

        state["mainwin"] = window

        #mainFrame.divideH()
        #mainFrame.divideV()

        #mainFrame.undivide()
        #mainFrame.undivide()

        window.resize(800, 600)

        #window.connect("focus-in-event", main_get_focus, None)

        window.show()

        def printmainframe(frame):
            print frame.tostring()

        state["keysemantics"].append( 
            ([Set([65507, 120]), Set([113])],
             lambda mv: printmainframe(mainFrame)
             )
            )

def main():
    gtk.main()
    return 0       

if __name__ == "__main__":
    MyEditor()
    main()

