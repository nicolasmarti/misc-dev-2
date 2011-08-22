
#
import sys
import os

# for ib
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from ib.ext.ScannerSubscription import ScannerSubscription

# for thread lock
from threading import *

# for time-related functions
from time import *
from datetime import *

# for Mysql
import MySQLdb

# for pyro
import Pyro.core
import Pyro.naming
import Pyro.constants
import Pyro.EventService.Clients

global scan 
global qqqq_id 

# the object exposed through pyro
class ServerInterface(Pyro.core.ObjBase):

	reqId = 0

        def __init__(self):
                Pyro.core.ObjBase.__init__(self)

	# contract

	def registercontract(self, contract):
		# look in the db if such a contract exists
		conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
		curs = conn.cursor()
		if contract.m_secType == 'STK': 
			curs.execute('select cid from ibcontract where symbol = %s and type = %s and exchange = %s and currency = %s', [contract.m_symbol, contract.m_secType, contract.m_exchange, contract.m_currency])
			result = curs.fetchall()                
			if len(result) == 0:
				# need to input the contract
				curs.execute("INSERT INTO ibcontract (symbol, type, exchange, currency, active) VALUES (%s, %s, %s, %s, %s)", [contract.m_symbol, contract.m_secType, contract.m_exchange, contract.m_currency, False])  
				cid = int(curs.lastrowid)
			else:
				cid = int(result[0][0])
			return(cid)
		# if yes, return the cid
		# else create the new contract and return the cid
		# -1 --> error
		return(-1)

        def isActiveContract(self, cid):
		conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
		curs = conn.cursor()
		curs.execute('select active from ibcontract where cid = %s', [cid])
		result = curs.fetchall()                
		if len(result) == 0: return(False)
		else: 
			res = result[0][0]
                #print res
			return(result[0][0])

        def activateContract(self, cid):
		if self.isActiveContract(cid) == 1:
			return(-1)
		else:
			conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
			curs = conn.cursor()
			curs.execute('update ibcontract set active = True where cid = %s', [cid])
			# how to get an error ??
			c = self.contractFromcid(cid)
			con.reqMktData(cid, c, '', False)
			return(0)

        def deActivateContract(self, cid):
		if self.isActiveContract(cid) == 0:
			return(-1)
		else:
			conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
			curs = conn.cursor()
			curs.execute('update ibcontract set active = False where cid = %s', [cid])
			# how to get an error ??
			c = self.contractFromcid(cid)
			con.cancelMktData(cid)
			return(0)

	def contractFromcid(self, cid):
		conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
		curs = conn.cursor()
		curs.execute('select * from ibcontract where cid = %s', [cid])
		result = curs.fetchall()                
		if len(result) == 0: return(None)
		c = Contract()
		c.m_symbol = result[0][1]
		c.m_secType = result[0][2]
		if result[0][3] != None: c.m_expiry = result[0][3]
		if result[0][4] != None: c.m_strike = result[0][4]
		if result[0][5] != None: c.m_right = result[0][5]
		c.m_exchange = result[0][6]
		if result[0][7] != None: c.m_currency = result[0][7]
		return(c)

	def contractDetail(self, cid):
		c = self.contractFromcid(cid)
		m_id = self.reqId
		self.reqId += 1
		con.reqContractDetails(m_id, c)
		return(m_id)

	def addstock(self, ticker, exchg, cur):
		#print ticker  + "  " + exchg  + "  " + cur
		c = Contract()
		c.m_symbol = ticker
		c.m_secType = 'STK'
		c.m_exchange = exchg
		c.m_currency = cur
		cid = self.registercontract(c)
		if not self.isActiveContract(cid):
			self.activateContract(cid)		
		return(cid)

	def addindex(self, ticker, exchg):
		c = Contract()
		c.m_symbol = ticker
		c.m_secType = 'IND'
		c.m_exchange = exchg
		cid = self.registercontract(c)
		if not self.isActiveContract(cid):
			self.activateContract(cid)		
		return(cid)


	def addfuture(self, ticker, exchg, expiry):
		c = Contract()
		c.m_symbol = ticker
		c.m_secType = 'FUT'
		c.m_exchange = exchg
		c.m_expiry = expiry
		cid = self.registercontract(c)
		if not self.isActiveContract(cid):
			self.activateContract(cid)		
		return(cid)


	def addoption(self, ticker, exchg, expiry, strike, right):
		c = Contract()
		c.m_symbol = ticker
		c.m_secType = 'OPT'
		c.m_exchange = exchg
		c.m_expiry = expiry
		c.m_strike = float(strike)
		c.m_right = right
		cid = self.registercontract(c)
		if not self.isActiveContract(cid):
			self.activateContract(cid)		
		return(cid)

	def positionContract(self, cid):
		conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
		curs = conn.cursor()
		curs.execute('select oid from iborder where cid = %s', [cid])    
		result = curs.fetchall()              
		size = 0
		rpnl = 0
		for i in result:
			(c, s, a, st) = self.positionOrder(i[0])
			size += s
			rpnl += -1 * a * s
		return(size, rpnl)		

	def closePosition(self, cid):
		conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
		curs = conn.cursor()
		curs.execute('select oid from iborder where cid = %s', [cid])    
		result = curs.fetchall()              
		for i in result:
			self.closeOrder(i[0])
		return(1)

	# order

	def placeOrder(self, cid, order):
		# first we enter the order
		conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
		curs = conn.cursor()
		curs.execute("INSERT INTO iborder (cid, action, totalquantity, ordertype, lmtprice, tif, openclose, status, pending) VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)", [cid, order.m_action, order.m_totalQuantity, order.m_orderType, order.m_lmtPrice, order.m_tif, order.m_openClose, 'Pending', order.m_totalQuantity])		
		oid = curs.lastrowid		
		c = self.contractFromcid(cid)
		order.m_orderId = oid
		order.m_transmit = True
		con.placeOrder(oid, c, order)
		return(oid)

	def cancelOrder(self, oid):
		con.cancelOrder(oid)
		return(oid)

	def closeOrder(self, oid):
		self.cancelOrder(oid)
		(cid, pos, avgprice, st) = self.positionOrder(oid)
		if pos == 0: return(-1)
		if pos > 0: action = "SELL"
		if pos < 0: action = "BUY"
		oid2 = self.addmktorder(action, abs(pos), "C", cid)
		return(oid2)

	def closelmtOrder(self, oid, price):
		self.cancelOrder(oid)
		(cid, pos, avgprice, st) = self.positionOrder(oid)
		if pos == 0: return(-1)
		if pos > 0: action = "SELL"
		if pos < 0: action = "BUY"
		oid2 = self.addlmtorder(action, abs(pos), "C", price, cid)
		return(oid2)

	def positionOrder(self, oid):
		# first get the cid
		conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
		curs = conn.cursor()
		curs.execute('select cid, action, status from iborder where oid = %s', [oid])    
		result = curs.fetchall()              
		if len(result) <> 1: return(-1)
		cid = result[0][0]
		status = result[0][2]
		if result[0][1] == "BUY": mult = 1
		else: mult = -1
		curs = conn.cursor()
		curs.execute('select size, price from orderexec where oid = %s order by id', [oid])    
		result = curs.fetchall()              		
		if (len(result) < 1): return (cid, 0, 0, status)
		return(cid, mult * result[len(result)-1][0], result[len(result)-1][1], status)

	def addmktorder(self, action, qty, oc, cid, tif = "DAY"):
		o = Order()
		o.m_action = action
		print tif
		o.m_tif = tif
		o.m_orderType = 'MKT'
		o.m_totalQuantity = qty
		o.m_openClose = oc
		res = self.placeOrder(cid, o)
		return(res)

	def addlmtorder(self, action, qty, oc, price, cid, tif = "DAY", date = ""):
		o = Order()
		o.m_action = action
		#print tif
		o.m_tif = tif
		o.m_orderType = 'LMT'
		o.m_totalQuantity = qty
		o.m_openClose = oc
		o.m_lmtPrice = float(round(price,2))
		o.m_goodTillDate = date
		res = self.placeOrder(cid, o)
		return(res)

	def pendingOrder(self, oid):
		conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
		curs = conn.cursor()
		curs.execute('select pending from iborder where oid = %s', [oid])    
		result = curs.fetchall()              
		return(result[0][0])

	# news
	def reqNews(self):
		con.reqNewsBulletins(True)
		return(1)

	def cancelNews(self):
		con.cancelNewsBulletins()
		return(1)


	# scan
	def mostactive(self, location, pricemin, pricemax):
		global scan 
		scan = []
		subscript = ScannerSubscription() 
		subscript.numberOfRows(200) 
		subscript.m_scanCode = 'MOST_ACTIVE' 
		subscript.m_instrument = 'STK' 
		subscript.m_averageOptionVolumeAbove = '' 
		subscript.m_couponRateAbove = '' 
		subscript.m_couponRateBelow = '' 
		subscript.m_abovePrice = pricemin 
		subscript.m_belowPrice = pricemax
		subscript.m_marketCapAbove = '' 
		subscript.m_marketCapBelow = '' 
		subscript.m_aboveVolume = '' 
		subscript.m_stockTypeFilter = 'ALL' 
		#subscript.locationCode('STK.NASDAQ.NMS') 
		#subscript.locationCode('STK.NYSE') 
		#subscript.locationCode('STK.AMEX') 
		subscript.locationCode(location) 
		con.reqScannerSubscription(qqqq_id, subscript) 
		sleep(10)
		return(scan)


	# Exit

        def exit(self):
            os._exit(0)

# the object to notice event

fieldname = ["BID", "BID", "ASK", "ASK", "LAST", "LAST", "HIGH", "LOW", "VOLUME", "CLOSE"]

class ServerPublisher(Pyro.EventService.Clients.Publisher):
    def __init__(self):
        Pyro.EventService.Clients.Publisher.__init__(self)
    def publishPrice(self, date, cid, type, quote):
	    #print "ContractPrice" + str(cid) + ": " + str((date, cid, fieldname[type], quote))
	    self.publish("ContractPrice" + str(cid), (date, cid, fieldname[type]+"PRICE", quote))	
    def publishSize(self, date, cid, type, quote):        
	    self.publish("ContractSize" + str(cid), (date, cid, fieldname[type]+"SIZE", quote))
    def orderStatus(self, date, oid, status, filled, avgprice, remaining):        
	    self.publish("OrderStatus" + str(oid), (date, oid, status, filled, avgprice, remaining))
    def publishNews(self, date, msgid, msgtype, news, origexchg):        
	    self.publish("News" + str(msgid), (date, msgid, msgtype, news, origexchg))
    def publishContractDetails(self, rid, details):        
	    self.publish("ContractDetails", (rid))

# IB message handler
def error_handler(msg):
    #lock.acquire()
    x = msg.values()
    #print "error: " + str(x)
    #lock.release()

def tick_handler(msg):
    #lock.acquire()
    x = msg.values()
    if x[1] in [1,2,4,6,7,9]:
        now = datetime.today().strftime("%Y-%m-%d %H:%M:%S");
	conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
	curs = conn.cursor()
        curs.execute("INSERT ibquoteprice values (%s, %s, %s, %s)", [now, x[0], fieldname[x[1]], x[2]])  
        sp.publishPrice(now, x[0],x[1],x[2])
    elif x[1] in [0,3,5,8,9]:
        now = datetime.today().strftime("%Y-%m-%d %H:%M:%S");
	conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
	curs = conn.cursor()
        curs.execute("INSERT ibquotesize values (%s, %s, %s, %s)", [now, x[0], fieldname[x[1]], x[2]])  
        sp.publishSize(now, x[0],x[1],x[2])
    else: 
        print x
    #lock.release()

def order_handler(msg):
    #lock.acquire()
    x = msg.values()
    oid = x[0]
    status = x[1]
    filled = x[2]
    remaining = x[3]
    avgprice = x[4]
    print "order: " + str(x)
    # typo
    conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
    curs = conn.cursor()
    curs.execute('select pending from iborder where oid = %s', [oid])    
    result = curs.fetchall()              
    # because of repeating of message
    now = datetime.today().strftime("%Y-%m-%d %H:%M:%S")
    if (result[0][0] > 0) and filled > 0:
	    curs.execute("INSERT INTO orderexec (oid, size, price, date) VALUES (%s, %s, %s, %s)", [oid, filled, avgprice, now])		    

    curs.execute('update iborder set status = %s, pending = %s where oid = %s', [status, remaining, oid])    
    sp.orderStatus(now, oid, status, filled, avgprice, remaining)
    #lock.release()

def news_handler(msg):
    #lock.acquire()
    x = msg.values()
    #print x
    now = datetime.today().strftime("%Y-%m-%d %H:%M:%S")
    sp.publishNews(now,x[0],x[1],x[2],x[3])
    #lock.release()

def contractdet_handler(msg):
    #lock.acquire()
    x = msg.values()
    #print "--------------"
    #print x
    #print x[1].m_summary
    #print x[1].m_marketName
    #print x[1].m_tradingClass
    #print x[1].m_minTick
    #print x[1].m_priceMagnifier
    #print x[1].m_orderTypes
    #print x[1].m_validExchanges
    #print x[1].m_underConId
    #print x[1].m_cusip
    #print x[1].m_ratings
    #print x[1].m_descAppend
    #print x[1].m_bondType
    #print x[1].m_couponType
    #print x[1].m_callable
    #print x[1].m_putable
    #print x[1].m_coupon
    #print x[1].m_convertible
    #print x[1].m_maturity
    #print x[1].m_issueDate
    #print x[1].m_nextOptionDate
    #print x[1].m_nextOptionType
    #print x[1].m_nextOptionPartial
    #print x[1].m_notes
    #print "--------------"
    sp.publishContractDetails(x[0], x[1].m_summary)
    #lock.release()

def subscriptdata_handler(msg):
	#lock.acquire()
	cd = msg.values()[2]
	#print (cd.m_summary.m_symbol, cd.m_summary.m_exchange, cd.m_summary.m_currency)
	scan.append((cd.m_summary.m_symbol, cd.m_summary.m_exchange, cd.m_summary.m_currency))
	#lock.release()

def subscriptdataend_handler(msg):
	#lock.acquire()
	global qqqq_id
	con.cancelScannerSubscription(qqqq_id) 
	qqqq_id += 2
	#lock.release()

def my_account_handler(msg):
    print "account: "+ str(msg)

def watcher(msg):
    print "watcher: " + str(msg)


# initialization

# DBMS

# Pyro init (requestloop will be executed at the end of the loop)
Pyro.core.initServer()
#ns=Pyro.naming.NameServerLocator().getNS()
#daemon=Pyro.core.Daemon()
#daemon.useNameServer(ns)

daemon=Pyro.core.Daemon('PYRO', 'localhost',8000)

si = ServerInterface()
uri=daemon.connect(si,"serverInterface")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri
sp = ServerPublisher()

# lock
lock = Lock()

# initialize cid
conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
curs = conn.cursor()
curs.execute('update ibcontract SET active = False where cid > 0')

scan = []
qqqq_id = 0

# Ib init
con = ibConnection("192.168.0.3")
print con
#con.registerAll(watcher)
con.register(tick_handler, message.TickSize)
con.register(tick_handler, message.TickPrice)
con.register(order_handler, message.OrderStatus)
con.register(error_handler, message.Error)
con.register(news_handler, message.UpdateNewsBulletin)
con.register(contractdet_handler, message.ContractDetails)
con.register(subscriptdata_handler, 'ScannerData')
con.register(subscriptdataend_handler, 'ScannerDataEnd')
con.register(my_account_handler, 'UpdateAccountValue')
con.connect()
#con.reqAccountUpdates(1, '')

# main loop = listening to pyro defined interface daemon
daemon.requestLoop()
