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
class Strat(Subscriber):

    def __init__(self, ticker, exchg, cur):
        Subscriber.__init__(self)

        self.cslock = Lock()

        # the timeseries

        self.bidprice = new TimeSeries([None, None, None, None])
        self.bidsize = new TimeSeries([None, None, None, None])
        
        self.askprice = new TimeSeries([None, None, None, None])
        self.asksize = new TimeSeries([None, None, None, None])
        
        self.lastprice = new TimeSeries([None, None, None, None])
        self.lastsize = new TimeSeries([None, None, None, None])

        self.highprice = new TimeSeries([None, None, None, None])
        
        self.lowprice = new TimeSeries([None, None, None, None])

        self.volumesize = new TimeSeries([None])

        self.closeprice = new TimeSeries([None, None, None, None])        

        # stock that we want

        o = Pyro.core.getProxyForURI("PYROLOC://localhost:8000/serverInterface")

        self.cid = o.addstock(ticker, exchg, cur)

        print "cid := " + str(self.cid)
        if (o.isActiveContract(self.cid) == 1):
            print "is already activated"
        else:
            print "activate := " + str(o.activateContract(self.cid))

        self.subscribe("ContractPrice" + str(self.cid))
        self.subscribe("ContractSize" + str(self.cid))

    def event(self, event):
        self.cslock.acquire()


        # first we enter the new value in our timeseries

        if event == "PRICE":
            
            date = event.msg[1]
            cid = event.msg[2]
            fieldname = event.msg[3]
            quote = event.msg[4]

            



        
        self.cslock.release()

    def buildgraph(self):
        
        ts = self.mts.getData()[0:self.graphperiod]

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

# start 
sub = Strat(sys.argv[1], sys.argv[2], sys.argv[3])
sub.listen()



