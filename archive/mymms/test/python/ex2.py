from Mymms import *
import types

try:
    c = mymmscommand(
        "Definition f A (x: A) := x."
        )
    print c
    print "normal: '" + getnormaloutput() + "'"
    print "error: '" + geterroroutput() + "'"
    print "debug: '" + getdebugoutput() + "'"
except:
    print "error: '" + geterroroutput() + "'"
    print "debug: '" + getdebugoutput() + "'"


try:
    c = mymmscommand(
        "Compute f."
        )
    print c
    print "normal: '" + getnormaloutput() + "'"
    print "error: '" + geterroroutput() + "'"
    print "debug: '" + getdebugoutput() + "'"
except:
    print "error: '" + geterroroutput() + "'"
    print "debug: '" + getdebugoutput() + "'"


