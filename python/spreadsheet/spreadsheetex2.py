from spreadsheet import *

ss = SpreadSheet()

# we try something
# a1 contains a value
# a2 compute a value with a1
# a3 compute also a value with a1
# a4 compute a value with a2 and a3

# test if a4 if really only updated once when updating a1

ss['a1'] = 12
ss["a2"] = "=a1+1"
ss["a3"] = "=a1+2"
ss["a4"] = "=a2+a3"

#print ss

ss._debug = True

ss["a1"] = 0

# seems that a4 is recomputed twice ... 

# another test, what in case of if ?
# if is a statement, not evaluable by eval ... so clear out the issue

ss2 = SpreadSheet()

ss2._debug = True

ss2["b"] = True

ss2["a"] = 1
ss2["c"] = 2

def ifte(test, true, false):
    if test:
        return true
    else:
        return false

def ift(test, true):
    if test:
        return true

def f(val):
    print "f(" + str(val) + ")"
    return val

ss2._globals.update(locals())

ss2["test"] = "=ifte(f(b), f(a), f(a))"

ss2["d"] = "=test + 2"

print ss2
