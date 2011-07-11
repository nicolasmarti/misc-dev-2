from spreadsheet import *

ss2 = SpreadSheet()

print "-----------------------------------------------------"
ss2._debug = True

ss2["b"] = True

ss2["prec"] = 10

ss2["a"] = "=prec + 1"
ss2["c"] = 2

def f(val):
    print val
    return val

ss2._globals.update(locals())

ss2["test"] = "= f(a + prec) if b else f(c)"

ss2["d"] = "=test + 2"

print ss2
print "-----------------------------------------------------"

ss2["c"] = 3

print ss2
print "-----------------------------------------------------"
ss2["b"] = False

print ss2
print "-----------------------------------------------------"
