import Pyro.core
import Pyro.naming
from Mymms import *

mymmsrequire("Float")

terms = dict()

class MymmsInterface(Pyro.core.ObjBase):
        def __init__(self):
                Pyro.core.ObjBase.__init__(self)
	def string2term(self, term):
		print "string2term"
		try:
			print "term := "
			print term
			a=pytypecheck(term)
			key = "{" + str(hex(id(a))) + "}"
			print "key:= "
			print key
			print "data := "
			print a
			terms[key] = a
		except:
			print "problem (if nothing --> lambda): "
			print sys.exc_info()
			key="ERROR"
		print "\n\n"
		return key

	def typeofterm(self, term):
		print "typeofterm"
		try:
			print term
			a = terms[term]
			print a
			type = a[3]
			print type
		except:
			print "problem:"
			print sys.exc_info()
			print terms
			type = "ERROR"
		print "\n\n"
		return type

	def valueofterm(self, term):
		print "valueofterm"
		try:
			print term
			a = terms[term]
			print a
			value = a[2]
			print value
		except:
			print "problem:"
			print sys.exc_info()
			print terms
			value = "ERROR"
		print "\n\n"
		return value

	def simplterm(self, fct, args):
		print "simplterm"
		try:
			print fct
			a = terms[fct]
			print "args = " + str(args)
			print terms
			b=[]
			for i in args:
				print i + " := "
				print terms[i]
				b = b + [terms[i][0]]
			a = simpl2(a[0], b)
			key = "{" + str(hex(id(a))) + "}"
			print "key:= "
			print key
			print "data := "
			print a
			terms[key] = a
			
		except:
			print "problem:"
			print sys.exc_info()
			print terms
			key = "ERROR"
		print "\n\n"
		return key

	def interpterm(self, fct, args):
		print "interpterm"
		try:
			print fct
			a = terms[fct]
			print "args = " + str(args)
			print terms
			b=[]
			for i in args:
				print i + " := "
				print terms[i]
				b = b + [terms[i][0]]
			a = interp2(a[0], b)
			key = "{" + str(hex(id(a))) + "}"
			print "key:= "
			print key
			print "data := "
			print a
			terms[key] = a
			
		except:
			print "problem:"
			print sys.exc_info()
			print terms
			key = "ERROR"
		print "\n\n"
		return key

Pyro.core.initServer()

# without name server
daemon=Pyro.core.Daemon("PYRO","localhost",7000)
uri=daemon.connect(MymmsInterface(),"mymmsint")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri

# with name server
#ns=Pyro.naming.NameServerLocator().getNS()
#daemon=Pyro.core.Daemon()
#daemon.useNameServer(ns)
#uri=daemon.connect(MymmsInterface(),"mymmsint")


daemon.requestLoop()
