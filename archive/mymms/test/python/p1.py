from Mymms import *


a=pytypecheck("\\A. \\(x:A).x")

print a

b=pytypecheck("\\(x: N). \\y. Nplus x y")

c=pytypecheck("45")
d=pytypecheck("45")

print b
print c
print d

e = simpl(b[0],c[0],d[0])
print e

e = interp(b[0],c[0],d[0])
print e

e = simpl2(b[0],[c[0],d[0]])
print e

e = interp2(b[0],[c[0],d[0]])
print e

e = interp2(b[0],[])
print e

f = mymms2python("\\(x: Float). \\y. Floatplus x y")

print (type(12.0))

print f(12.0,13.0)

f2=mymms2python("\\x. \\y. (Floatplus 1.0 (Floatplus x y))")

print f2(0.0,-1.5)

f2

mymmsrequire("Num")
mymmsrequire("Float")

f = b=pytypecheck("\\(x: Float) y. x  + y")

a = pytypecheck("0.9")

r = interp2(f[0],[a[0],a[0]])
