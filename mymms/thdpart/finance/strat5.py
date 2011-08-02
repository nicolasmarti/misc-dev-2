import Pyro.core
from threading import *
from time import sleep
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from Pyro.EventService.Clients import Subscriber
from datetime import *
from time import *
from timeseries import *
from types import *
from thread import *
import os as os
import sys


from pylab import *
from matplotlib.finance import quotes_historical_yahoo, candlestick, plot_day_summary, candlestick2
from matplotlib.dates import  DateFormatter, WeekdayLocator, HourLocator, DayLocator, MONDAY, timezone
import numpy as np
import matplotlib.colors as colors
import matplotlib.finance as finance
import matplotlib.ticker as mticker
import matplotlib.mlab as mlab
import matplotlib.pyplot as plt
import matplotlib.font_manager as font_manager

# interface object

# the strategy
class Strat(Subscriber, Thread):

    tostop = False

    def run(self):
        try:
            self.listen()
        except:
            print self.ticker + " thread ended"
            return(None)
        o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")
        res = o.positionOrder(self.oid)
        if res <> -1:
            (cid, pos, avgprice) = res
            self.oid = o.closeOrder(self.oid)        


    def stop(self):
        self.tostop = True

    def __init__(self, ticker, exchg, cur):

        Thread.__init__(self)
        Subscriber.__init__(self)

        # initialize all the datastructure
        self.cslock = Lock()
        self.ticker = ticker
        
        self.tsers = {}
        self.tsers["LASTPRICE"] = TimeSeries([])
        self.tsers["BIDPRICE"] = TimeSeries([])
        self.tsers["ASKPRICE"] = TimeSeries([])
        self.tsers["HIGHPRICE"] = TimeSeries([])
        self.tsers["LOWPRICE"] = TimeSeries([])
        self.tsers["CLOSEPRICE"] = TimeSeries([])
        self.tsers["BIDSIZE"] = TimeSeries([])
        self.tsers["ASKSIZE"] = TimeSeries([])
        self.tsers["LASTSIZE"] = TimeSeries([])
        self.tsers["VOLUMESIZE"] = TimeSeries([])

        # first element: name
        # second element: init element
        # third computation of the current element

        self.indicators = [("SMA9", None, 
                            lambda x: self.tsers["LASTPRICE"].SMA(9, 0, lambda x: x[3])                            
                            ), 
                           ("SMA6", None, 
                            lambda x: self.tsers["LASTPRICE"].SMA(6, 0, lambda x: x[3])                            
                            )
                           ]

        for i in self.indicators:
            self.tsers[i[0]] = TimeSeries([])

        self.newbar = {}
        self.newbar["lasttime"] = 0.0
        self.newbar["timeout"] = 10.0  
        self.newbar["volumeout"] = 3000 
        
        # stock that we want
        o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")
        self.cid = o.addstock(ticker,exchg,cur)
        if (not (o.isActiveContract(self.cid) == 1)):
            o.activateContract(self.cid)

        self.ticker = ticker

        # suscribe
        self.subscribe("ContractPrice" + str(self.cid))
        self.subscribe("ContractSize" + str(self.cid))

        self.state = "CLOSED"

    def event(self, event):
        self.cslock.acquire()

        # are we setting a new bar ???
        if self.neednewbar1():           
            for i in ["LASTPRICE", "BIDPRICE", "ASKPRICE", "HIGHPRICE", "LOWPRICE", "CLOSEPRICE"]:
                ts = self.tsers[i]
                ts.addData([None,None,None,None])
            for i in ["BIDSIZE", "ASKSIZE", "LASTSIZE", "VOLUMESIZE"]:
                ts = self.tsers[i]
                if ts.length() == 0:
                    ts.addData([0, 0])
                else:
                    ts.addData([0, ts[0][1] + ts[0][0]])
            for i in self.indicators:
                self.tsers[i[0]].addData(i[1])
            #print str(self.tsers)


        # update the bar value
        date = event.msg[0]
        cid = event.msg[1]
        fieldname = event.msg[2]
        quote = event.msg[3]
        #print event.msg
        
        # update tser

        # a PRICE field
        if fieldname in ["LASTPRICE", "BIDPRICE", "ASKPRICE", "HIGHPRICE", "LOWPRICE", "CLOSEPRICE"]:
            ts = self.tsers[fieldname]
            # new or old bar
            if ts[0][3] == None:
                ts[0] = [quote, quote, quote, quote]
            else:
                ts[0][3] = quote
                if ts[0][1] < quote:
                    ts[0][1] = quote
                if ts[0][2] > quote:
                    ts[0][2] = quote

            
        else:
            ts = self.tsers[fieldname]
            ts[0][0] = quote - ts[0][1]
        
        # compute indicators
        for i in self.indicators:
            self.tsers[i[0]][0] = i[2](None)
        
        
        # execute strategy

        ts = self.tsers["LASTPRICE"]



        if self.state == "CLOSED":

            try:
                if self.tsers["SMA6"][0] > self.tsers["SMA9"][0]:

                    o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

                    self.size = int(5000/ts[0][3])

                    self.oid = o.addlmtorder("BUY", self.size, "O", ts[0][3], self.cid, "DAY")                    

                    self.opentime = time()

                    self.state = "OPENING"
                    print self.ticker + ": CLOSED -> OPENING"

            except:
                print "exception in CLOSED"
                print sys.exc_info()

        elif self.state == "OPENING":

            try:

                o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

                res = o.positionOrder(self.oid)

                if res <> -1:
                    
                    (cid, pos, avgprice, status) = res

                    self.state = OPENED

                else:

                    self.timout = 20

                    if time() > self.opentime + self.timeout:

                        o.cancelOrder(self.oid)
                        
                        self.state = "CANCELLINGOPENING"
                        print self.ticker + ": OPENING -> CANCELLINGOPENING"

            except:
                print "exception in OPENING"
                print sys.exc_info()


        elif self.state == "CANCELLINGOPENING":
            
            try:

                o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

                res = o.positionOrder(self.oid)

                if res <> -1:
                    
                    (cid, pos, avgprice, status) = res

                    if status == "Cancelled": 
                        self.state = "CANCELLEDOPENING" 
                        print self.ticker + ": CANCELLINGOPENING -> CANCELLEDOPENING"
                
            except:
                print "exception in CANCELLINGOPENING"
                print sys.exc_info()

        elif self.state == "CANCELLEDOPENING":
            
            try:

                o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

                res = o.positionOrder(self.oid)

                (cid, pos, avgprice, status) = res

                if pos > 0:
                    self.state = "OPENED"
                    print self.ticker + ": CANCELLEDOPENING -> OPENED"
                else:
                    self.state = "CLOSED"
                    print self.ticker + ": CANCELLEDOPENING -> CLOSED"
                
            except:
                print "exception in CANCELLEDOPENING"
                print sys.exc_info()


        elif self.state == "OPENED":

            try:

                o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

                (cid, pos, avgprice, status) = o.positionOrder(self.oid)

                upnl = (self.mts.getData()[0][3] - avgprice) * pos

                if self.tsers["SMA9"][0] > self.tsers["SMA6"][0]:

                    self.oid = o.addlmtorder("SELL", self.size, "C", ts[0][3], self.cid, "DAY")        

                    self.closetime = time()

                    self.state = "CLOSING"
                    print self.ticker + ": OPENED -> CLOSING"

                elif upnl < -40:
                    
                    self.oidc = o.closeOrder(self.oid)

                    self.state = "CLOSING"
                    print self.ticker + ": OPENED -> CLOSING"

                elif upnl > 40: 

                    self.oidc = o.closeOrder(self.oid)

                    self.state = "CLOSING"
                    print self.ticker + ": OPENED -> CLOSING"


            except:
                print "exception in OPENED"
                print sys.exc_info()

        elif self.state == "CLOSING":

            try:
                o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

                res = o.positionOrder(self.oidc)

                if res <> -1:
                    
                    (cid, pos, avgprice, status) = res

                    self.state = OPENED
                    print self.ticker + ": CLOSING -> OPENED"

                else:

                    self.timout = 20

                    if time() > self.opentime + self.timeout:

                        o.cancelOrder(self.oidc)
                        
                        self.state = "CANCELLINGCLOSING"
                        print self.ticker + ": CLOSING -> CANCELLINGCLOSING"

            except:
                print "exception in OPENING"
                print sys.exc_info()

        elif self.state == "CANCELLINGCLOSING":
            
            try:

                o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

                res = o.positionOrder(self.oidc)

                if res <> -1:
                    
                    (cid, pos, avgprice, status) = res

                    if status == "Cancelled": 
                        self.state = "CANCELLEDCLOSING"      
                        print self.ticker + ": CANCELLINGCLOSING -> CANCELLEDCLOSING"
                
            except:
                print "exception in CANCELLINGCLOSING"
                print sys.exc_info()

        elif self.state == "CANCELLEDCLOSING":
            
            try:

                o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

                res = o.positionOrder(self.oid)

                (cid, pos, avgprice, status) = res

                if pos > 0:
                    self.state = "OPENED"
                    print self.ticker + ": CANCELLEDCLOSING -> OPENED"
                else:
                    self.state = "CLOSED"
                    print self.ticker + ": CANCELLEDCLOSING -> CLOSED"
                
            except:
                print "exception in CANCELLEDCLOSING"
                print sys.exc_info()
         

        self.cslock.release()

    # function based on time
    def neednewbar1(self):
        l = time() - self.newbar["lasttime"]
        if l > self.newbar["timeout"]:
            self.newbar["lastbar"] = time()            
            return True
        else:
            return False

    # function based on volume
    def neednewbar2(self):      
        if self.tsers["VOLUMESIZE"].length() == 0: return True
        if self.tsers["VOLUMESIZE"][0][0] > self.newbar["volumeout"]:
            return True
        else:
            return False


    def buildgraph(self):
        
        ts = self.mts.getData()#[0:self.graphperiod]

        left, width = 0.1, 0.9
        rect1 = [left, 0.05, width, 0.99]
        size = len(ts) * 0.2
        if size >= 32768:
            size = 31767
        fig = figure(figsize = (size, 10))
        
        axescolor  = '#f6f6f6'
        
        ax = fig.add_axes(rect1, axisbg=axescolor)  #left, bottom, width, height

        # build the series for candles

        M = []        
        t = len(self.mts.getData())
        for i in ts:
            M.insert(0, (t, i[0], i[3], i[1], i[2], 0))
            t -= 1

        candlestick(ax, M, width=0.6)

        M1 = []
        M2 = []
        M3 = []
        t2 = 1
        for i in ts:
            if i[4] == None or i[5] == None:
                t2 += 1
            else:
                M1.insert(0, i[4] + self.K2 * i[5])
                M2.insert(0, i[4])
                M3.insert(0, i[4] - self.K * i[5])

        date=range(t2+t,t+t2+len(M1))
        ax.plot(date, M1)
        ax.plot(date, M2)
        ax.plot(date, M3)

        for i in self.open:
            if i[0] >= t:
                ax.plot([i[0]], [i[1]], 'o', color='cyan')

        for i in self.close:
            if i[2] == "stoploss" and i[0] >= t:
                ax.plot([i[0]], [i[1]], 'o', color='red')
            elif i[2] == "stopgain" and i[0] >= t:
                ax.plot([i[0]], [i[1]], 'o', color='green')
            elif i[2] == "stopuptrend" and i[0] >= t:
                ax.plot([i[0]], [i[1]], 'o', color='yellow')
            elif i[2] == "timeout(open)" and i[0] >= t:
                ax.plot([i[0]], [i[1]], 'o', color='blue')
            elif i[2] == "timeout(close)" and i[0] >= t:
                ax.plot([i[0]], [i[1]], 'o', color='blue')

        now = datetime.today().strftime("-%Y-%m-%d-%H-%M-%S");

        filename = "./charts/" + sys.argv[1] + ".png"
        fig.savefig(filename)



o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

stocks = []
stocks2 = []
print stocks


threads = {}

pricemin = '70'
pricemax = '500'

while True:
    global stocks, stocks2    
    stocks2 = o.mostactive('STK.NYSE', pricemin, pricemax)
    stocks2 += o.mostactive('STK.NASDAQ.NMS', pricemin, pricemax)
    stocks2 += o.mostactive('STK.AMEX', pricemin, pricemax)

    print stocks2

    maxsize = 40
    stocks2 = stocks2[0:min(maxsize, len(stocks2)-1)]

    if len(stocks2):
    
        d1 = set(map((lambda x: x[0]), stocks))
        d2 = set(map((lambda x: x[0]), stocks2))

        remove = d1 - d2
        add = d2 - d1

        print "-------------------------------\n\n"
        print "remove: " + str(remove)
        print "add: " + str(add)
        print "actives: " + str(d2)
        print "stock2: " + str(stocks2)
        print "-------------------------------\n\n"

        for i in remove:
            threads[i].abort()
            threads[i].join()
            del threads[i]

        for i in stocks2:
            if i[0] in add and not (i[0] in threads.keys()): 
                #print " -- add --" + i[0]
                try:
                    sub = Strat(i[0], i[1], i[2])
                    threads[i[0]] = sub
                    sub.start()                    
                    print " -- added --" + i[0]
                except :
                    print " -- cannot add --" + i[0]
                
        

        stocks = stocks2
    
    sleep(60*60*30)
    

