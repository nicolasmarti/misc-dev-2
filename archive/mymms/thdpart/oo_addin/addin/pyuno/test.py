import Pyro.core
import uno
import unohelper
from types import *

myHost = ''
myPort = 50007

from com.sun.star.lang import IllegalArgumentException, Locale

# pythonloader looks for a static g_ImplementationHelper variable
g_ImplementationHelper = unohelper.ImplementationHelper()

# used for storing supported interfaces of classes 
g_TypeTable = {}

display2prog = {'FUNLAMBDA': 'funlambda', 
		'TERMTYPE': 'termtype', 
		'TERMVALUE': 'termvalue', 
		'SIMPLTERM': 'simplterm',
		'INTERPTERM': 'interpterm'
		}
prog2display = {'funlambda': 'FUNLAMBDA', 
		'termtype': 'TERMTYPE', 
		'termvalue': 'TERMVALUE', 
		'simplterm': 'SIMPLTERM',
		'interpterm': 'INTERPTERM'
		}
argumentsnames = {'funlambda': ['term'], 
		  'termtype': ['term'], 
		  'termvalue': ['term'], 
		  'simplterm': ['fonction','args'],
		  'interpterm': ['fonction','args']
		  }
argumentsdescriptions = {'funlambda': ['the term'], 
			 'termtype': ['the term'], 
			 'termvalue': ['the term'], 
			 'simplterm': ['fonction','args'],
			 'interpterm': ['fonction','args']
			 }
fctdescriptions = {'funlambda': 'FUNLAMBDA', 
		   'termtype': 'TERMTYPE', 
		   'termvalue': 'TERMTYPE', 
		   'simplterm': 'SIMPLTERM',
		   'interpterm': 'INTERPTERM'
		   }
diplaycategories = {'FUNLAMBDA': 'funlambda', 
		    'TERMTYPE': 'termtype', 
		    'TERMVALUE': 'termvalue', 
		    'SIMPLTERM': 'simplterm',
		    'INTERPTERM': 'interpterm'		    
		    }
progcategories = {'funlambda': 'mymms', 
		  'termtype' : 'mymms', 
		  'termvalue' : 'mymms', 
		  'simplterm' : 'mymms',
		  'interpterm': 'mymms'
		  } 

class MymmsAddin:
	def __init__(self, ctx):
		self.ctx = ctx	# store the default context for later use
		
		self.ServiceName = "org.openoffice.sheet.addin.MymmsAddin"
		self.AddInService = "com.sun.star.sheet.AddIn"
		self.ImplementationName = "org.openoffice.sheet.addin.MymmsAddin"
		self.SupportedServiceNames = (self.ServiceName, self.AddInService,)
		
		self.Locale = -1
		
	# XTypeProvider method implementations	
	def getTypes (self):
		global g_TypeTable
		
		if g_TypeTable.has_key (self.__class__):
			ret = g_TypeTable[self.__class__]
		else:
			ret = (
				uno.getTypeByName( "org.openoffice.sheet.addin.MymmsAddin" ),
				uno.getTypeByName( "com.sun.star.sheet.XAddIn" ),
				uno.getTypeByName( "com.sun.star.lang.XLocalizable" ),
				uno.getTypeByName( "com.sun.star.lang.XServiceName" ),
				uno.getTypeByName( "com.sun.star.lang.XServiceInfo" ),
				uno.getTypeByName( "com.sun.star.lang.XTypeProvider" ),
				)
			g_TypeTable[self.__class__] = ret
			
		return ret
	
	def getImplementationId (self):
		return uno.generateUuid ()
	
	# XServiceName method implementations
	def getServiceName(self):		
		return self.ServiceName
	
	# XServiceInfo method implementations	
	def getImplementationName (self):
		return self.ImplementationName
	
	def supportsService(self, ServiceName):
		return (ServiceName in self.SupportedServiceNames)
	
	def getSupportedServiceNames (self):
		return self.SupportedServiceNames
	
	# MymmsAddin method implementations
	def funlambda(self, nValue):
		res=""
		if type(nValue) == TupleType:
			for i in nValue:
				for j in i:
					res = res + str(j) + " "
		else:
			res=str(nValue)
		o = Pyro.core.getProxyForURI("PYROLOC://localhost:7000/mymmsint")
		#o = Pyro.core.getProxyForURI("PYRONAME://mymmsint")
		return o.string2term(res)

	def termtype(self, nValue):
		o = Pyro.core.getProxyForURI("PYROLOC://localhost:7000/mymmsint")
		#o = Pyro.core.getProxyForURI("PYRONAME://mymmsint")
		return o.typeofterm(nValue)

	def termvalue(self, nValue):
		o = Pyro.core.getProxyForURI("PYROLOC://localhost:7000/mymmsint")
		#o = Pyro.core.getProxyForURI("PYRONAME://mymmsint")
		return o.valueofterm(nValue)


		
	def any2term(self, value, o):		
		if value <> None:
			if type(value) == TupleType or type(value) == ListType:
				margs = []
				for i in value:
					margs = margs + self.any2term(i, o)
				return margs					
			else:
				v = str(value)
				if len(v) == 0:
					return []
				else:
					if (v[0] == "{") and (value[len(v) - 1] == "}"):
						return [v]
					else:						
						return [o.string2term(v)]				
		else:
			return[]

	def simplterm(self, fct, args):
		o = Pyro.core.getProxyForURI("PYROLOC://localhost:7000/mymmsint")
		#o = Pyro.core.getProxyForURI("PYRONAME://mymmsint")
		margs = self.any2term(args, o)
		return o.simplterm(fct, margs)
		
	def interpterm(self, fct, args):
		o = Pyro.core.getProxyForURI("PYROLOC://localhost:7000/mymmsint")
		#o = Pyro.core.getProxyForURI("PYRONAME://mymmsint")
		margs = self.any2term(args, o)
		return o.interpterm(fct, margs)

	# XAddIn method implementations
	def getProgrammaticFuntionName(self, aDisplayName):
		# Attention: The method name contains a spelling error. 
		# Due to compatibility reasons the name cannot be changed.
		return display2prog[aDisplayName]
		
	def getDisplayFunctionName(self, aProgrammaticName):
		return prog2display[aProgrammaticName]
	
	def getFunctionDescription(self, aProgrammaticName):
		return fctdescriptions[aProgrammaticName]

	def getDisplayArgumentName(self, aProgrammaticFunctionName, nArgument):
		return argumentsnames[aProgrammaticFunctionName][nArgument]
	
	def getArgumentDescription(self, aProgrammaticFunctionName, nArgument):
		return argumentsdescriptions[aProgrammaticFunctionName][nArgument]
	
	def getProgrammaticCategoryName(self, aProgrammaticFunctionName):
		return progcategories[aProgrammaticFunctionName]
	
	def getDisplayCategoryName(self, aProgrammaticFunctionName):
		return diplaycategories[aProgrammaticFunctionName]
	
	# XLocalizable method implementations
	def setLocale(self, eLocale):
		# the locale is stored and used for getLocale, but otherwise
		# ignored at the moment
		self.Locale = eLocale

	def getLocale(self):
		return self.Locale

	
g_ImplementationHelper.addImplementation( 
	MymmsAddin, 
	"org.openoffice.sheet.addin.MymmsAddin", 	
	("org.openoffice.sheet.addin.MymmsAddin", "com.sun.star.sheet.AddIn"),)



# end module
