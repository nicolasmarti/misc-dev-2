from spreadsheet import *

ss2 = SpreadSheet()

ss2._debug = True

ss2["b"] = True

ss2["a"] = 1
ss2["c"] = 2

def f(val):
    print val
    return val

ss2._globals.update(locals())

ss2["test"] = "= f(a) if b else f(c)"

ss2["d"] = "=test + 2"

ss2["c"] = 3

ss2["b"] = False
