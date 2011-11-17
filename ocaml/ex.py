

res = Doudou.proceed("\
Tree (A :: Type) :: Type := \
| Leaf :: Tree A \
| Node :: A -> Tree A -> Tree A -> Tree A")

#print res
#print dir(Doudou)

te = Doudou.Tree(Doudou.Type)

print "Tree Type := " + str(te)

print "|Tree Type| := " + str(len(te))

#del(te)

#Doudou.undo()

#print dir(Doudou)

res = Doudou.proceed("\
nat :: Type := \
| O :: nat \
| S :: nat -> nat")

O = Doudou.O
S = Doudou.S

print O.type()
print S.type()

print S(O)

#print dir(Doudou)
