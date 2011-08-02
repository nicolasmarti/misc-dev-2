from Mymms import *

from numpy import *


mymmsrequire("Float")
f2=mymms2python("\\ x y. 1.0 / (1.0 + (0.01 * (x * x)) + (0.5 * (y * y)))")

def f(x,y):
    return 1.0 / (1.0 + (0.01 * (x **2)) + (0.5 * (y**2)))

print f2

import Gnuplot, Gnuplot.funcutils
g = Gnuplot.Gnuplot(debug=1)

x = arange(35)*2.0
y = arange(30)/10.0 - 1.5
g('set parametric')
g('set data style lines')
g('set hidden')
g('set contour base')
g.title('An example of a surface plot')
g.xlabel('x')
g.ylabel('y')



def f1(x,y):
    #x1=str(x)
    x2 = float(x)
    #print (x,type(x), x1, type(x1), x2, type(x2))
    #y1=str(y)
    y2 = float(y)
    #print (y,type(y),y1,type(y1), y2, type(y2))
    #res = 1.0 / (1 + 0.01 * x**2 + 0.5 * y**2)
    #print res
    #res2=f2(x1,y1)
    #print res2
    res3 = f2(x2,y2)
    #print res3
    #print "\n"
    return res3


g.splot(Gnuplot.funcutils.compute_GridData(x,y, f1, binary=0))

raw_input('Please press return to continue...\n')

def f(x,y):
    return 1.0 / (1.0 + (0.01 * (x **2)) + (0.5 * (y**2)))

g.splot(Gnuplot.funcutils.compute_GridData(x,y, f, binary=0))

raw_input('Please press return to continue...\n')

