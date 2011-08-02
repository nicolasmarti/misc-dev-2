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




# the strategy
class Strat(Subscriber, Thread):

    def run(self):
        self.listen()

    def __init__(self, ticker, exchg, cur):
        Thread.__init__(self)
        Subscriber.__init__(self)

        self.cslock = Lock()
        self.mts = TimeSeries([])
        self.lastbar = 0.0
        self.position = "CLOSED"
        self.opentimeout = 10
        self.closetimeout = 10
        self.triggertimeout = 60
        self.oid = -1
        self.oidc = -1

        self.ticker = ticker

        self.size = 100

        self.open = []
        self.close = []

        o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

        # stock that we want
        self.cid = o.addstock(ticker,exchg,cur)

        print "cid := " + str(self.cid)
        if (o.isActiveContract(self.cid) == 1):
            print "is already activated"
        else:
            print "activate := " + str(o.activateContract(self.cid))


        # test values
        self.size = 100
        self.barperiod = 10
        self.N = 9
        self.K = 1.8
        self.K2 = 1.8
        self.graphperiod = 6
        self.opentimeout = 5
        self.closetimeout = 1
        self.stoplossN = 0.005
        self.stopgainN = 0.01
        self.mingainN = 20.0/self.size
        self.maxlossN = 20.0/self.size

        self.part = 0.9995

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
        if fieldname == "LAST":

            #print event

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

            
            if mu <> None and sig <> None:

                cur[4] = mu
                cur[5] = sig
                cur[6] = (cur[3] - mu)/sig
                try:
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
                        (cid, pos, avgprice) = res
                        if pos == 0:

                            if time() - self.opentime > self.opentimeout:
                                print self.ticker + ": OPENED -> CLOSED (timeout)"
                                self.position = "CLOSED"
                                self.close.append((len(self.mts.getData()), self.mts.getData()[0][3], "timeout(open)"))
                                self.oidc = o.closeOrder(self.oid)        
                                self.closetime = time()

                        else:
                            #print (avgprice - self.mts.getData()[0][3])/avgprice
                            if (avgprice - self.mts.getData()[0][3])/avgprice > self.stoplossN or (avgprice - self.mts.getData()[0][3]) > self.maxlossN:
                                print self.ticker + ": " + str((avgprice, self.mts.getData()[0][3]))
                                self.position = "CLOSED"
                                print self.ticker + ": OPENED -> CLOSED (stoploss)"
                                self.close.append((len(self.mts.getData()), self.mts.getData()[0][3], "stoploss"))
                                self.oidc = o.closelmtOrder(self.oid, self.mts.getData()[0][3])        
                                self.closetime = time()
                                
                            # if a reverse marteau in 
                            elif self.mts.getData()[1][0] < self.mts.getData()[1][3] and (self.mts.getData()[1][3] - self.mts.getData()[1][0])/(self.mts.getData()[1][1] - self.mts.getData()[1][2]) < 1/4 and (self.mts.getData()[1][3] - self.mts.getData()[1][2])/(self.mts.getData()[1][1] - self.mts.getData()[1][2]) < 1/4:

                                price = self.mts.getData()[0][3] * self.part
                                print self.ticker + ": " + str((avgprice,price))
                                self.position = "CLOSED"
                                print self.ticker + ": OPENED -> CLOSED (stopuptrend)"
                                self.close.append((len(self.mts.getData()), price, "stopuptrend"))
                                self.oidc = o.closelmtOrder(self.oid, price)        
                                self.closetime = time()

                            elif (((self.mts.getData()[0][3] - avgprice)/avgprice > self.stopgainN) and (self.mts.getData()[0][3] - avgprice) > self.mingainN): 

                                price = self.mts.getData()[0][3] * self.part
                                print self.ticker + ": " + str((avgprice, price))
                                #print str((self.mts.getData()[0][3] - avgprice)/avgprice) + " > " + str(self.stopgainN) + " and " + str(self.mts.getData()[0][3] - avgprice) + " > " + str(self.mingainN)
                                self.position = "CLOSED"
                                print self.ticker + ": OPENED -> CLOSED (stopgain1)"
                                self.close.append((len(self.mts.getData()), price, "stopgain"))
                                self.oidc = o.closelmtOrder(self.oid, price)        
                                self.closetime = time()

                            elif (self.mts.getData()[0][3] >= mu + (self.K2 * sig)) and ((self.mts.getData()[0][3] - avgprice) > self.mingainN): 
                                                            
                                price = self.mts.getData()[0][3] * self.part
                                print self.ticker + ": " + str((avgprice, price))
                                #print str(self.mts.getData()[0][3]) + " >= " + str(mu + (self.K2 * sig)) + " and " + str(self.mts.getData()[0][3] - avgprice) + " > " + str(self.mingainN)
                                self.position = "CLOSED"
                                print self.ticker + ": OPENED -> CLOSED (stopgain2)"
                                self.close.append((len(self.mts.getData()), price, "stopgain"))
                                self.oidc = o.closelmtOrder(self.oid, price)        
                                self.closetime = time()



                #print (mu - self.mts.getData()[0][3])/sig

                # we are closed and we get long on supposed low
                # len(fstocsma[cid]) > 0
                if self.position == "CLOSED":                    
                    o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")
                    res = o.positionOrder(self.oidc)
                    #print res
                    if res <> -1 and res[1] == 0:                            
                        if time() - self.closetime > 5 * self.closetimeout:
                            o.closeOrder(self.oidc)        
                            self.close.append((len(self.mts.getData()), self.mts.getData()[0][3], "timeout(close)"))
                            self.oidc = o.closeOrder(self.oid)        
                            self.closetime = time()
                            print self.ticker + ": CLOSED (timeout, mkt) --> " + str(self.mts.getData()[0][3])
                        elif time() - self.closetime > self.closetimeout:
                            price = self.mts.getData()[0][3] * self.part
                            o.closeOrder(self.oidc)        
                            self.close.append((len(self.mts.getData()), price, "timeout(close)"))
                            self.oidc = o.closelmtOrder(self.oid, price)   
                            self.closetime = time()
                            print self.ticker + ": CLOSED (timeout, lmt) --> " + str(price)
                    else:
                        ls = 4
                        if self.mts.getData()[0][3] <= mu - (self.K * sig) and len(self.mts.getData()) > ls + self.N:                            
                            if ksma <> None and cur[6] > ksma:
                                self.position = "OPENED"
                                print self.ticker + ": CLOSED -> OPENED(long)"
                                self.open.append((len(self.mts.getData()), self.mts.getData()[0][3]))                            
                                self.oid = o.addlmtorder('BUY', self.size, 'O', self.mts.getData()[0][3], self.cid)
                                self.opentime = time()
                               
        
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

stocks = [("GS","NYSE","USD"), 
          ("MS","NYSE","USD"), 
          ("JPM", "NYSE","USD"),
          ("DB", "NYSE","USD"),
          ("CS", "NYSE","USD"),
          ("HBC", "NYSE","USD"),
          ("WFC","NYSE","USD"),
          ("IBM", "NYSE","USD"), 
          ("SNE", "NYSE","USD"), 
          ("HPQ", "NYSE","USD"),
          ("ORCL", "SMART","USD"), 
          ("YHOO", "SMART","USD"), 
          ("AAPL", "SMART","USD"), 
          ("GOOG","SMART","USD"), 
          ("MSFT", "SMART","USD"), 
          ("PALM", "SMART","USD") 
          ]

threads = []
for i in stocks:
    print " -- Begin --" + i[0]
    sub = Strat(i[0], i[1], i[2])
    threads.append(sub)
    sub.start()
    print " -- End --" + i[0]
    print ""

for i in threads:
    i.join()


