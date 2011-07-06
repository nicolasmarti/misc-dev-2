from math import sin, pi

from spreadsheet import *

ss = SpreadSheet()

ss._globals = globals()

ss['a1'] = 5
ss['a2'] = '=a1*6'
ss['a4'] = '=a1*6'
ss['a3'] = '=a2*7'
assert ss['a3'] == 210
ss['b1'] = '=sin(pi/4)'
assert ss['b1'] == 0.70710678118654746
assert ss.getformula('b1') == '=sin(pi/4)'
print str(ss._cells)
print str(ss._dep)
ss['a1'] = 12
print str(ss._cells)
print str(ss._dep)
