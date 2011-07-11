from spreadsheet import *

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
