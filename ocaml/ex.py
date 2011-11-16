

res = Doudou.proceed("\
Tree (A :: Type) :: Type := \
| Leaf :: Tree A \
| Node :: A -> Tree A -> Tree A -> Tree A")

#print res
print dir(Doudou)
print Doudou.Tree
print Doudou.Type

print "Tree Type := " + str(Doudou.Tree(Doudou.Type))

#print (Doudou.Tree)
#print (Doudou.Type)

#ty = Doudou.Tree(Doudou.Type)
#print "ty := " + str(ty)
