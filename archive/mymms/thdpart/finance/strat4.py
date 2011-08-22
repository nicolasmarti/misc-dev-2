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


#

def gttime(n):
    t = datetime.today()+timedelta(seconds=n)
    return (t, t.strftime("%Y%m%d %H:%M:%S"))


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
        #o.closePosition(self.cid)

    def __init__(self, ticker, exchg, cur):

        Thread.__init__(self)
        Subscriber.__init__(self)

        self.cslock = Lock()
        self.mts = TimeSeries([])
        self.lastbar = 0.0
        self.position = "CLOSED"
        self.triggertimeout = 60
        self.oid = -1
        self.oidc = -1

        self.ticker = ticker

        self.open = []
        self.close = []

        o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

        # stock that we want
        self.cid = o.addstock(ticker,exchg,cur)

        #print "cid := " + str(self.cid)
        if (not (o.isActiveContract(self.cid) == 1)):
            o.activateContract(self.cid)


        # test values
        self.barperiod = 10
        self.N = 9
        self.K = 1.8
        self.K2 = 1.5
        self.graphperiod = 6
        self.opentimeout = 10
        self.closetimeout = 5
        self.stoplossN = 0.005
        self.stopgainN = 0.01
        self.mingainN = 10
        self.maxlossN = 25.0

        self.profittimeout = 60*10

        self.part = 0.9998

        self.lastgraph = 0.0
        self.subscribe("ContractPrice" + str(self.cid))

    def event(self, event):
        self.cslock.acquire()

        # get the different data of the message
        date = event.msg[0]
        cid = event.msg[1]
        fieldname = event.msg[2]
        quote = event.msg[3]

        # look for time
        l = time() - self.lastbar

        #l2 = time() - self.lastgraph

        #if l2 > self.graphperiod * self.barperiod:
        #    if len(self.mts.getData()) > 0: self.buildgraph()
        #    self.lastgraph = time()            

        # update current bar
        if fieldname == "LASTPRICE":

            #print self.ticker + ": " + str(event)

            # need to build a new bar
            if l > self.barperiod:
                self.lastbar = time()            
                self.mts.addData([quote,quote,quote,quote, None, None, None])

            #print event.msg
            cur = self.mts.getData()[0]
            cur[3] = quote
            if cur[1] < quote:
                cur[1] = quote
            if cur[2] > quote:
                cur[2] = quote

            self.mts.setData(cur)

            mu = self.mts.SMA(self.N, 0, lambda x: x[3])
            sig = self.mts.stdev(self.N, 0, lambda x: x[3])

            
            if mu <> None and (sig <> None or sig <> 0):

                cur[4] = mu
                cur[5] = sig
                
                try:
                    cur[6] = (cur[3] - mu)/sig
                    ksma = self.mts.SMA(4, 0, lambda x: x[6])
                except:
                    ksma = None

                self.mts.setData(cur)

                # strat1
                # The stop-loss
                if self.position == "OPENED":
                    o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")
                    res = o.positionOrder(self.oid)
                    #print res
                    if res <> -1:
                        (cid, pos, avgprice, status) = res
                        #print "order " + str(self.oid) + " position := " + str(res)
                        #print "stock " + self.ticker + " uP&L: " + str((self.mts.getData()[0][3] - avgprice) * pos)
                        upnl = (self.mts.getData()[0][3] - avgprice) * pos
                        if (avgprice - self.mts.getData()[0][3]) > self.stoplossN * avgprice:
                            self.closetime = gttime(80)
                            self.oidc = o.addlmtorder("SELL", pos, "C", self.mts.getData()[0][3], self.cid, "GTD", self.closetime[1])
                            print self.ticker + ": " + str((avgprice, self.mts.getData()[0][3]))
                            self.position = "CLOSED"
                            print self.ticker + ": OPENED -> CLOSED (stoploss1) :=" + str(self.oidc)
                            #self.close.append((len(self.mts.getData()), self.mts.getData()[0][3], "stoploss"))

                        elif (avgprice - self.mts.getData()[0][3]) * pos > self.maxlossN:
                            self.closetime = gttime(80)
                            print self.ticker + ": " + str((avgprice, self.mts.getData()[0][3]))
                            self.oidc = o.addlmtorder("SELL", pos, "C", self.mts.getData()[0][3], self.cid, "GTD", self.closetime[1])
                            self.position = "CLOSED"
                            print self.ticker + ": OPENED -> CLOSED (stoploss2) :=" + str(self.oidc)
                            #self.close.append((len(self.mts.getData()), self.mts.getData()[0][3], "stoploss"))

                            # if a reverse marteau in 
                            #elif self.mts.getData()[1][0] < self.mts.getData()[1][3] and (self.mts.getData()[1][3] - self.mts.getData()[1][0])/(self.mts.getData()[1][1] - self.mts.getData()[1][2]) < 1/4 and (self.mts.getData()[1][3] - self.mts.getData()[1][2])/(self.mts.getData()[1][1] - self.mts.getData()[1][2]) < 1/4:

                            #price = self.mts.getData()[0][3] * self.part
                            #print self.ticker + ": " + str((avgprice,price))
                            #self.position = "CLOSED"
                            #print self.ticker + ": OPENED -> CLOSED (stopuptrend)"
                            #self.close.append((len(self.mts.getData()), price, "stopuptrend"))
                            #self.oidc = o.closelmtOrder(self.oid, price)        
                            #self.closetime = time()

                        elif (((self.mts.getData()[0][3] - avgprice) > self.stopgainN * avgprice) and (self.mts.getData()[0][3] - avgprice) * pos > self.mingainN): 

                            #price = self.mts.getData()[0][3] * self.part
                            #print self.ticker + ": " + str((avgprice, price))
                            self.closetime = gttime(80)
                            self.oidc = o.addlmtorder("SELL", pos, "C", self.mts.getData()[0][3], self.cid,"GTD", self.closetime[1])
                            #print str((self.mts.getData()[0][3] - avgprice)/avgprice) + " > " + str(self.stopgainN) + " and " + str(self.mts.getData()[0][3] - avgprice) + " > " + str(self.mingainN)
                            self.position = "CLOSED"
                            print self.ticker + ": OPENED -> CLOSED (stopgain1) :=" + str(self.oidc)
                            #self.close.append((len(self.mts.getData()), price, "stopgain"))

                        elif (self.mts.getData()[0][3] >= mu + (self.K2 * sig)) and ((self.mts.getData()[0][3] - avgprice) > self.mingainN): 
                            self.closetime = gttime(80)
                            price = self.mts.getData()[0][3] * self.part
                            print self.ticker + ": " + str((avgprice, price))
                            self.oidc = o.addlmtorder("SELL", pos, "C", price, self.cid,"GTD", self.closetime[1])
                            #print str(self.mts.getData()[0][3]) + " >= " + str(mu + (self.K2 * sig)) + " and " + str(self.mts.getData()[0][3] - avgprice) + " > " + str(self.mingainN)
                            self.position = "CLOSED"
                            print self.ticker + ": OPENED -> CLOSED (stopgain2) :=" + str(self.oidc)
                            #self.close.append((len(self.mts.getData()), price, "stopgain"))

                        elif upnl > 2 and  datetime.today() > self.opentime[0]+timedelta(minutes=10): 
                            
                            self.closetime = gttime(80) 
                            #price = self.mts.getData()[0][3] * self.part
                            #print self.ticker + ": " + str((avgprice, price))
                            self.oidc = o.addlmtorder("SELL", pos, "C", self.mts.getData()[0][3], self.cid,"GTD", self.closetime[1])
                            #print str(self.mts.getData()[0][3]) + " >= " + str(mu + (self.K2 * sig)) + " and " + str(self.mts.getData()[0][3] - avgprice) + " > " + str(self.mingainN)
                            self.position = "CLOSED"
                            print self.ticker + ": OPENED -> CLOSED (stopgain3) :=" + str(self.oidc)
                            #self.close.append((len(self.mts.getData()), price, "stopgain"))



                #print (mu - self.mts.getData()[0][3])/sig

                # we are closed and we get long on supposed low
                # len(fstocsma[cid]) > 0

                if self.position == "CLOSED":                    
                    o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

                    if (o.positionContract(self.cid))[0] > 0:
                        self.position = "OPENED"
                        print self.ticker + ": CLOSED -> OPENED (late)"

                    else:
                        res = o.positionOrder(self.oidc)
                        if res <> -1 and self.closetime[0] > datetime.today():                            
                        
                            o.cancelOrder(self.oidc)
                            print self.ticker + ": CLOSED -> OPENED (timeout) :=" + str(self.oidc)
                            self.position = "OPENED"
                            self.close.append((len(self.mts.getData()), self.mts.getData()[0][3], "timeout(close)"))

                        else:

                            ls = 4
                            if self.mts.getData()[0][3] <= mu - (self.K * sig) and len(self.mts.getData()) > ls + self.N:                            
                                if ksma <> None and cur[6] <> None and  cur[6]>ksma:
                                    self.open.append((len(self.mts.getData()), self.mts.getData()[0][3]))                            
                                    self.size = int(5000/self.mts.getData()[0][3])
                                    self.opentime = gttime(80)
                                    self.oid = o.addlmtorder('BUY', self.size, 'O', self.mts.getData()[0][3], self.cid, "GTD", self.opentime[1])
                                    self.position = "OPENED"
                                    print self.ticker + ": CLOSED -> OPENED(long) :=" + str(self.oid)
                               
        
        self.cslock.release()

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

pricemin = '50'
pricemax = '200'

while True:
    global stocks
    stocks2 = o.mostactive('STK.NYSE', pricemin, pricemax)
    stocks2 += o.mostactive('STK.NASDAQ.NMS', pricemin, pricemax)
    stocks2 += o.mostactive('STK.AMEX', pricemin, pricemax)

    maxsize = 80
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
    
    sleep(60*60*10)
    

