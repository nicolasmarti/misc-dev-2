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

print ss

ss._debug = True

ss["a1"] = 0

# seems that a4 is recomputed twice ... 
