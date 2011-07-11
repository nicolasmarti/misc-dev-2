from spreadsheet import *

# another test, what in case of if ?
# if is a statement, not evaluable by eval ... so clear out the issue
# yet with the following setup, ifte computes all its args ...

ss2 = SpreadSheet()

ss2._debug = True

ss2["b"] = True

ss2["a"] = 1
ss2["c"] = 2

def f(val):
    print "f(" + str(val) + ")"
    return val

ss2._globals.update(locals())

# ugly workaround
ss2["test"] = "=ifte(f(b), lambda self : f(self['c'] + 8), lambda self : f(self['a']))"

ss2["d"] = "=test + 2"

print ss2

ss2["c"] = 0

print ss2

ss2["b"] = False

print ss2

# does not work -> test does not depends on a ...

ss2["a"] = 2

print ss2

