from Mymms import *

from numpy import *

import Gnuplot, Gnuplot.funcutils

x = arange(30)/10.0 - 1.5
y = arange(30)/10.0 - 1.5

g = Gnuplot.Gnuplot(debug=0)
g('set parametric')
g('set data style lines')
g('set hidden')
g('set contour base')
g.title('An example of a surface plot')
g.xlabel('x')
g.ylabel('y')

mymmsrequire("Float")

f2=mymms2python("\\(x: Float). \\y. (x * x) + (y * y) + (x * y)")

def f1(x,y):
    x2 = float(x)
    y2 = float(y)
    res3 = f2(x2,y2)
    return res3


g.splot(Gnuplot.funcutils.compute_GridData(x,y, f1, binary=0))
#g.hardcopy('gp_test.png', "png")

raw_input('Please press return to continue...\n')

