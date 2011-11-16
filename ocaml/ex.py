

res = Doudou.proceed("\
Tree (A :: Type) :: Type := \
| Leaf :: Tree A \
| Node :: A -> Tree A -> Tree A -> Tree A")

#print res
print dir(Doudou)

print "Tree Type := " + str(Doudou.Tree(Doudou.Type))

Doudou.undo()

print dir(Doudou)
