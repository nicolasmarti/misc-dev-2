# this class is supposed to somehow emulate an emacs inputs of key
# this is supposed to be derived
from sets import *

class KeyBinding:

    def __init__(self):
        
        # the set of pressed keys
        self.pressed_key = Set()

        # the set of keybinding
        # basically a [([Set keycode]), self -> ()]
        self.keyactions = []

        # the latest longest valid key sequences
        self.validkeysequences = []

        # there is a special keycode for control
        self.ctrl = 0
        

    # this function is call when a key is pressed
    def keypressed(self, keycode):
        # we add the key pressed to the set
        self.pressed_key.add(keycode)
        # and call the manager
        self.managekey()

    # this function is call when a key is released
    def keyreleased(self, keycode):
        # discard the key from the set
        self.pressed_key.discard(keycode)


    # the key manager: decide if the current list of entered key is a valid one,
    # and run the action
    def managekey(self):

        #print "validkeysequence:" + str(self.validkeysequences)

        #print "pressed_key:" + str(self.pressed_key)

        # initially the validity id false
        valid = False
        # we do a traversal of all the key actions
        for i in self.keyactions:
            # if the valid keysequence so far is not empty
            if len(i[0]) > len(self.validkeysequences):
                # we make a fold that will check if the sequence is a prefix of the currently checked keyactions
                prefix = True
                for j in range(0, len(self.validkeysequences) - 1):
                    prefix = prefix and (self.validkeysequences[j] == i[0][j])
                    
                #if prefix: 
                #    print "prefix"
                #else:
                #    print "not a prefix"

                # yes this is a prefix
                if prefix:
                    valid = True
                    # is the pressed key is the following sequence we were waiting for
                    if self.pressed_key == i[0][len(self.validkeysequences)]:
                        # append to validsequence
                        self.validkeysequences.append(self.pressed_key)
                        # if if this is the final one 
                        if len(self.validkeysequences) == len(i[0]):
                            # then we can execute the action
                            # we reset the sequence
                            self.validkeysequences = []
                            # clear the presed key
                            self.pressed_key = Set()
                            # and call the actions
                            #print "runaction"
                            i[1](self)
                            return

                        

        # it is not a valid sequence
        if not valid:
            # we reset the validkeysequence
            self.validkeysequences = []

