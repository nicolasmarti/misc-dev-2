from Mymms import *
import types

t = "\\x. \\y. (Zplus x y) "
f = mymms2python(t)
print f(2,3)
print type(f(2,3))

t1 = "\\x. \\y. (Floatplus x y) "
f1 = mymms2python(t1)
print f1(2.0,3.0)
print type(f1(2.0,3.0))

mymmsrequire("Num")
mymmsrequire("Ord")

print (pytypecheck("Neq"))
print (pytypecheck("@Lt"))
print (pytypecheck("\\ x y.  if (Neq x y) then Eq else (if (Nlt x y) then Lt else Gt)"))
print (pytypecheck("Nplus"))
print (pytypecheck("Nmultiply"))
print (pytypecheck("Nminus"))
print (pytypecheck("Ndivide"))
print (pytypecheck("isNum Nplus Nmultiply Nminus Ndivide"))
print (pytypecheck("isOrd (\\ x y.  if (Neq x y) then Eq  else (if (Nlt x y) then Lt else Gt))"))
print (pytypecheck("@isOrd"))
print (pytypecheck("@Ord"))

mymmsrequire("Option")
mymmsrequire("Prod")

print (pytypecheck("@Some"))

mymmsrequire("Logic")
mymmsrequire("List")
mymmsrequire("N")
mymmsrequire("Z")

mymmsload("ext")

t2 = "\\ (x: StdLib.string.String) -> x "
f2 = mymms2python(t2)
print f2("doudou")
print type(f2("doudou"))

print "'" + getnormaloutput() + "'"
