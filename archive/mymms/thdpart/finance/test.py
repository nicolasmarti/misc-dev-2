#from Mymms import *
import types
import sys
import os
from curses import *
from time import sleep
from ib.ext.Contract import Contract
from ib.ext.Order import Order
from ib.opt import ibConnection, message
from threading import *
import sqlite3

from datetime import *
from time import *

import MySQLdb

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



#all the fields name
fieldname = ["bid size", "bid", "ask", "ask size", "last", "last size", "high", "low", "volume", "close"]

#displayed field
fieldprint = [1,2,4,8]

# size for printing a field
sizefield = 0

# computed here
for i in fieldname:
    s = len(i)
    if sizefield < s:
        sizefield = s
sizefield += 3

# size of asset names
namesize = 8

# keep the most recent data for each contracts for each field (to implement green/red printing)
data = []

# list of contracts
contracts = []

# current position for each contract
positions = []

# current contract
curcontract = 0

# current field
curfield = 0

# global P&L
gpnl = [0]

# lock
lock = Lock()

# list of orders
orders = [[]]

# not used yet
(maxy, maxx) = (0,0)

# market data historic in forms of bar (indice, Open, High, Low, Close, Volume)
bars = []

# ask price
ask = []

# bid price
bid = []

# last bar time
lastbar = [0.0]

# bar period in second
barperiod = 60*5

# indicators

#bollinger band
bollinger_middle = []
bollinger_stddev = []
N = 15
K = 2
stdk = []
def update_bollinger(cid):    
    try:
        sum1 = 0
        for i in range(0,N):
            if bars[cid][i][4] != None:
                sum1 += bars[cid][i][4]
        sum1 /= N

        if len(bollinger_middle[cid]) + N <= len(bars[cid]):
            bollinger_middle[cid].insert(0, sum1)
        else:
            bollinger_middle[cid][0] = sum1
            
        if len(bollinger_middle[cid]) >= N:
            sum2 = 0
            for i in range(0,N):
                if bars[cid][i][4] != None:
                    sum2 += ((bollinger_middle[cid][i] - bars[cid][i][4]) ** 2)/N
            sum2 = sqrt(sum2)

            stdn = (bars[cid][i][4] - sum1) / sum2

            stdscr.addstr(((cid+1)) + 1, ((len(fieldprint)+7)*sizefield) + namesize, str(stdn) + "    ")        
                   
            if len(bollinger_stddev[cid]) + N <= len(bollinger_middle[cid]):
                bollinger_stddev[cid].insert(0,sum2)
                stdk[cid].insert(0,stdn)
            else:
                bollinger_stddev[cid][0] = sum2
                stdk[cid][0] = stdn

    except: 
        return

# fast stochastic oscillator
fstoc = []
KN = 15
def update_fstoc(cid):    
    try:
        if len(bars[cid]) >= KN and bars[cid][0][4] != None and bars[cid][0][3] != None and bars[cid][0][2] != None:

            lastclose = bars[cid][0][4]
            lowlowestn = bars[cid][0][3]
            highhighestn = bars[cid][0][2]

            if lastclose != None and lowlowestn != None and highhighestn != None:
                for i in range(0,KN):
                    if bars[cid][i][3] != None and bars[cid][i][3] < lowlowestn:
                        lowlowestn = bars[cid][i][3]
                    if bars[cid][i][2] != None and bars[cid][i][2] > highhighestn:
                        highhighestn = bars[cid][i][2]

                k = ((lastclose - lowlowestn)/(highhighestn - lowlowestn)) * 100        

                if len(fstoc[cid]) + KN <= len(bars[cid]):
                    fstoc[cid].insert(0, k)
                else:
                    fstoc[cid][0] = k
    except:
        return
            
# SMA fast stochastic oscillator
fstocsma = []
Nfstoc = 3
def update_fstocsma(cid):    
    try:
        if len(fstoc[cid]) >= Nfstoc:

            sum = 0
            for i in range(0,Nfstoc):
                if fstoc[cid][i] != None:
                    sum += fstoc[cid][i]
            sum /= Nfstoc
            
            if len(fstocsma[cid]) + Nfstoc <= len(fstoc[cid]):
                fstocsma[cid].insert(0, sum)
            else:
                fstocsma[cid][0] = sum
    except: return

# RSI
RSIN = 15
RSI = []
def update_rsi(cid):    

    if len(bars[cid]) > RSIN and bars[cid][0][4] != None and bars[cid][0][3] != None and bars[cid][0][2] != None:

        U = []
        D = []
        
        for i in range(0,RSIN):
            if bars[cid][i][4] != None and bars[cid][i+1][4] != None:
                if bars[cid][i][4] > bars[cid][i+1][4]:
                    U.append(bars[cid][i][4] - bars[cid][i+1][4])
                    D.append(0)
                else:
                    D.append(bars[cid][i+1][4] - bars[cid][i][4])
                    U.append(0)

        #alpha=2.0/(RSIN+1.0)
        valU = 0
        valD = 0
        #U.reverse()
        #D.reverse()
        #for i in range(0,len(U)):
        #    valU = valU*(1-alpha) + U[i]*alpha
            #valU += U[i]
        try:
            for i in U:
                valU += i
            valU /= len(U)
        except: return

        try:
            for i in D:
                valD += i
            valD /= len(D)
        except: return

        #for i in range(0,len(D)):
        #    valD = valD*(1-alpha) + D[i]*alpha
            #valD += D[i]
        #valD /= len(D)

        try:
            if (valD <> 0): val = 100 - 100/(1+(valU/valD))
            else: val = 50
        except: return
            
        #stdscr.addstr(49, 5, "alpha := " + str(alpha) + "                  ")                
        #stdscr.addstr(50, 5, "U := " + str(U) + "                  ")                
        #stdscr.addstr(51, 5, "D := " + str(D) + "                  ")                
        #stdscr.addstr(52, 5, "valU := " + str(valU) + "                  ")                
        #stdscr.addstr(53, 5, "valD := " + str(valD) + "                  ")                

        if len(RSI[cid]) + RSIN <= len(bars[cid]):
            RSI[cid].insert(0, val)
        else:
            RSI[cid][0] = val

            
# ADX
ADXN = 15
ADX = []
ADX2 = []
def update_adx(cid):    
    try:
        if len(bars[cid]) > ADXN and bars[cid][0][4] != None and bars[cid][0][3] != None and bars[cid][0][2] != None:

            PDM = []
            MDM = []
        
            TR = []

            for i in range(0, ADXN):
                if bars[cid][i][2] != None and bars[cid][i+1][2] != None and bars[cid][i][3] != None and bars[cid][i+1][3] != None:
                    upmove = bars[cid][i][2] - bars[cid][i+1][2]
                    downmove = bars[cid][i+1][3] - bars[cid][i][3]

                    if upmove > downmove and upmove > 0:  
                        PDM.append(upmove)
                    else:
                        PDM.append(0)
                        
                    if downmove > upmove and downmove > 0:  
                        MDM.append(downmove)
                    else:
                        MDM.append(0)
                            
                    TR.append(max(bars[cid][i][2], bars[cid][i+1][4]) - min(bars[cid][i][3], bars[cid][i+1][4]))
                            
            alpha=2.0/(ADXN+1.0)
                            
            # ---------------------
                            
            PDM.reverse()
            MDM.reverse()
            TR.reverse()
 
            ATR = 0
            PDI = 0
            MDI = 0        
            for i in range(0,len(TR)):
                ATR = ATR*(1-alpha) + TR[i]*alpha

            for i in range(0,len(PDM)):
                    PDI = PDI*(1-alpha) + PDM[i]*alpha
            PDI /= ATR
                    
            for i in range(0,len(MDM)):
                MDI = MDI*(1-alpha) + MDM[i]*alpha
            MDI /= ATR

            if (PDI + MDI) <> 0: val = 100 * (PDI - MDI)/(PDI + MDI)
            else: val = 0

            if len(ADX2[cid]) + ADXN <= len(bars[cid]):
                ADX2[cid].insert(0, val)
            else:
                ADX2[cid][0] = val

        #stdscr.addstr(52, 0, str(ADX2) + "      ")        
        #stdscr.refresh()        
    
        # ---------------------

        #stdscr.addstr(50, 0, str(len(PDM)) + " : " + str(PDM) + "      ")        
        #stdscr.addstr(51, 0, str(len(MDM)) + " : " + str(MDM) + "      ")        
        #stdscr.addstr(52, 0, str(len(TR)) + " : " + str(TR) + "      ")        
        #stdscr.refresh()        

            PDI = []
            MDI = []

            for i in range(0,len(PDM)):
                PDI.append(PDM[i]*100/TR[i])   
                MDI.append(MDM[i]*100/TR[i])   

        #stdscr.addstr(53, 0, str(PDI) + "      ")        
        #stdscr.addstr(54, 0, str(MDI) + "      ")        
        #stdscr.refresh()        

            val = 0
            n = 0

            tab = []
        
            for i in range(0,len(PDI)):
                if (MDI[i]+PDI[i]) <> 0:
                    tab.append((abs(MDI[i]-PDI[i])/(MDI[i]+PDI[i]))*100)
                #val += (abs(MDI[i]-PDI[i])/(MDI[i]+PDI[i]))*100

            for i in tab:
                val += i

            if len(tab) > 0:
                val /= len(tab)

            #stdscr.addstr(55, 0, "val := " + str(val) + "      ")        
            #stdscr.refresh()        

            if len(ADX[cid]) + ADXN <= len(bars[cid]):
                ADX[cid].insert(0, val)
            else:
                ADX[cid][0] = val


        #stdscr.addstr(40, 0, str(ADX) + "      ")        
        #stdscr.addstr(50, 0, str(ADX2) + "      ")        
        #stdscr.refresh()        
    except:
        return

# swing trading strategy

strat1position = []
strat1lock = Lock()


start1mul = 3

stopgain = 0.15 * start1mul
maxstopgain = 100

stoplossN = 3 * start1mul
maxstoploss = -300

def strat1(cid):

    try:
        if bars[cid][1][5] ==0  or abs(bars[cid][1][4] - bars[cid][0][4])/bars[cid][0][4] > 0.1: return
    except:
        return

    strat1lock.acquire()

    # The stop-loss

    if strat1position[cid] == "OPENED" and bars[cid][0][4] != None  and bid[cid][0] <> None and ask[cid][0] <> None:
        if computeupnl(positions[cid][0], bid[cid][0], ask[cid][0]) < max(- stoplossN * bars[cid][0][4], maxstoploss):
            strat1position[cid] = "STOPPED"
            stdscr.addstr(((cid+1)) + 1, ((len(fieldprint)+6)*sizefield) + namesize, str(strat1position[cid]) + "   ")        
            closepos(cid)        
            strat1lock.release()
            return

    
    # we are closed and we get long on supposed low
    # len(fstocsma[cid]) > 0 
    if strat1position[cid] == "CLOSED" and len(fstoc[cid]) > 0 and  len(bollinger_middle[cid]) > 0 and len(bollinger_stddev[cid]) > 0 and bars[cid][0][4] != None and ADX2[cid][0] <> None and len(fstocsma[cid]) > 0:
        if bars[cid][0][4] <= bollinger_middle[cid][0] - (K * bollinger_stddev[cid][0]): # and ADX2[cid][0] < -60  and RSI[cid][0] < 30 and fstoc[cid][0] < 10 and fstocsma[cid][0] < 10: 
            strat1position[cid] = "WAITING"
            stdscr.addstr(((cid+1)) + 1, ((len(fieldprint)+6)*sizefield) + namesize, str(strat1position[cid]) + "   ")        
            addlmtorder(cid, 'BUY', bars[cid][0][4], 100 * start1mul)
            strat1lock.release()
            return

    # we are open and we close our position on a supposed high
    # and len(fstocsma[cid]) > 0  and len(fstoc[cid]) > 0  and ADX2[cid][0] <> None
    if strat1position[cid] == "OPENED" and len(bollinger_middle[cid]) > 0 and len(bollinger_stddev[cid]) > 0 and bars[cid][0][4] <> None and bid[cid][0] <> None and ask[cid][0] <> None:
        # hitting the roof !!!
        #if bars[cid][0][4] >= bollinger_middle[cid][0] + (K * bollinger_stddev[cid][0]) and fstoc[cid][0] > 95 and computeupnl(positions[cid][0], bid[cid][0], ask[cid][0]) > 5 and RSI[cid][0] > 80 and ADX2[cid][0] > 65: 
        #    strat1position[cid] = "CLOSED"
        #    stdscr.addstr(((cid+1)) + 1, ((len(fieldprint)+6)*sizefield) + namesize, str(strat1position[cid]) + "   ")        
        #    closepos(cid)        
        #    strat1lock.release()
        #    return

        # hitting the median ( )
        if bars[cid][0][4] >= bollinger_middle[cid][0] + (1 * bollinger_stddev[cid][0]): 
            strat1position[cid] = "CLOSED"
            stdscr.addstr(((cid+1)) + 1, ((len(fieldprint)+6)*sizefield) + namesize, str(strat1position[cid]) + "   ")        
            closepos(cid)        
            strat1lock.release()
            return

        #stopgain
        #if computeupnl(positions[cid][0], bid[cid][0], ask[cid][0]) >= min(bars[cid][0][4] * stopgain, maxstopgain) : 
        #    strat1position[cid] = "CLOSED"
        #    stdscr.addstr(((cid+1)) + 1, ((len(fieldprint)+6)*sizefield) + namesize, str(strat1position[cid]) + "   ")        
        #    closepos(cid)        
        #    strat1lock.release()
        #    return

    strat1lock.release()
    return

# functions

def addcontract(c, other = None):    
    contracts.append(c)
    data.append([0 for i in range(0,11)])
    positions.append(([], 0))

    bollinger_middle.append([])
    bollinger_stddev.append([])
    fstoc.append([])
    fstocsma.append([])
    RSI.append([])
    ADX.append([])
    ADX2.append([])
    stdk.append([])

    strat1position.append("STOPPED")

    bars.append([[None, None,None,None,None,0]])
    ask.append([[None]])
    bid.append([[None]])
    con.reqMktData(len(contracts)-1, c, '', False)
    stdscr.addstr((len(contracts))+1, 0, c.m_symbol)
    if other != None:
        stdscr.addstr((len(contracts))+1, (len(fieldprint) * sizefield) + namesize, other)

def addstock(ticker, exchg, cur = None):
    c = Contract()
    c.m_symbol = ticker
    c.m_secType = 'STK'
    c.m_exchange = exchg
    if cur != None:
        c.m_currency = cur
    addcontract(c, "Stock(" + exchg + ")")

def addindex(ticker, exchg):
    c = Contract()
    c.m_symbol = ticker
    c.m_secType = 'IND'
    c.m_exchange = exchg
    addcontract(c, "Index(" + exchg + ")")

def addfutur(ticker, exchg, expiry):
    c = Contract()
    c.m_symbol = ticker
    c.m_secType = 'FUT'
    c.m_exchange = exchg
    c.m_expiry = expiry
    addcontract(c, "Fut(" + exchg + ", " + expiry + ")")

def addoption(ticker, exchg, expiry, strike, right):
    c = Contract()
    c.m_symbol = ticker
    c.m_secType = 'OPT'
    c.m_exchange = exchg
    c.m_expiry = expiry
    c.m_strike = float(strike)
    c.m_right = right
    addcontract(c, "Opt(" + exchg + ", " + expiry + ", " + str(strike) + ", " + right +")")

def addmktorder(cid, action, qty):
    id = len(orders)
    o = Order()
    o.m_orderId = id
    o.m_clientId = 0
    o.m_permid = 0
    o.m_action = action
    o.m_lmtPrice = 0
    o.m_auxPrice = 0
    o.m_tif = 'DAY'
    o.m_orderType = 'MKT'
    o.m_totalQuantity = qty
    o.m_transmit = True
    orders.append([o, cid, qty, id])        
    con.placeOrder(id, contracts[cid], o)
    position(cid)
    pending(cid)

def addlmtorder(cid, action, price, qty):
    id = len(orders)
    o = Order()
    o.m_orderId = id
    o.m_action = action
    o.m_orderType = 'LMT'
    o.m_tif = 'DAY'
    o.m_totalQuantity = qty

    o.m_clientId = 0
    o.m_permId = 0
    o.m_lmtPrice = float(round(price,2))
    #o.m_auxPrice = float(price)

    orders.append([o, cid, qty, id])        
    con.placeOrder(id, contracts[cid], o)
    position(cid)
    pending(cid)

def closepos(cid):
    # first cancel pending order
    #stdscr.addstr(50, 10, str(orders))    
    for i in orders:
        if len(i) > 0:
            if i[1] == cid and i[2] <> 0:
                con.cancelOrder(i[3])
    l = positions[cid][0]
    sum = 0
    for i in l:
        sum += i[0]
    if sum < 0:
        addmktorder(cid, 'BUY', abs(sum))
    if sum > 0:
        addmktorder(cid, 'SELL', abs(sum))

def closeposlmt(cid, price):
    # first cancel pending order
    #stdscr.addstr(50, 10, str(orders))    
    for i in orders:
        if len(i) > 0:
            if i[1] == cid and i[2] <> 0:
                con.cancelOrder(i[3])
    l = positions[cid][0]
    sum = 0
    for i in l:
        sum += i[0]
    if sum < 0:
        addlmtorder(cid, 'BUY', price, abs(sum))
    if sum > 0:
        addlmtorder(cid, 'SELL', price, abs(sum))

def storeval(val, cid):
    #
    if bars[cid][0][0] == None :
        bars[cid][0][0] = len(bars[cid])
    # Open
    if bars[cid][0][1] == None :
        bars[cid][0][1] = val
    # High
    if val > bars[cid][0][2] or bars[cid][0][2] == None:
        bars[cid][0][2] = val
    # Low
    if val < bars[cid][0][3] or bars[cid][0][3] == None:
        bars[cid][0][3] = val
    # Close
    bars[cid][0][4] = val

def storevol(vol, cid):
    bars[cid][0][5] += vol

def mprint(tickid, field, value, color):
    v = str(value)
    for i in range(0,sizefield - len(str(value))):
        v += " "
    stdscr.addstr((tickid)+2, (field * sizefield) + namesize, v, color)

def printgpnl():
    stdscr.addstr(len(contracts)+5, 5, "P&L := ")
    if gpnl[0] >= 0:
        stdscr.addstr(len(contracts)+5, 12, str(gpnl[0]) + "               ", color_pair(2))
    else:
        stdscr.addstr(len(contracts)+5, 12, str(gpnl[0]) + "               ", color_pair(1))

def computeupnl(l, bid, ask):
    sum = 0
    for i in l:
        if i[0] > 0:
            sum += (i[0] * (bid - i[1]))
        if i[0] < 0:
            sum += (i[0] * (ask - i[1]))
            
    return(sum)

def position(tickid):
    sum = 0
    for i in positions[tickid][0]:
        sum += i[0]
    if sum >= 0:
        mprint(tickid, (len(fieldprint)+4), str(sum) + "     ", color_pair(2))
    else:
        mprint(tickid, (len(fieldprint)+4), str(sum) + "     ", color_pair(1))

def pending(tickid):
    sum = 0
    for i in orders:
        if len(i) > 0 and i[1] == tickid:
            if (i[0].m_action == "BUY"):
                mul = 1
            else:
                mul = -1
            sum += mul * i[2]
 
    if sum >= 0:
        mprint(tickid, (len(fieldprint)+5), str(sum) + "     ", color_pair(2))
    else:
        mprint(tickid, (len(fieldprint)+5), str(sum) + "     ", color_pair(1))
        
    
def tick_handler(msg):
    lock.acquire()
    x = msg.values()
    if x[1] <= 9: 
        d = data[x[0]][x[1]]
        data[x[0]][x[1]] = x[2]

        if x[2] > d and x[1] in fieldprint:            
            mprint(x[0], fieldprint.index(x[1]), x[2], color_pair(2))

        if x[2] < d and x[1] in fieldprint:            
            mprint(x[0], fieldprint.index(x[1]), x[2], color_pair(1))

        if x[2] == d  and x[1] in fieldprint:            
            mprint(x[0], fieldprint.index(x[1]), x[2], color_pair(3))

        if x[1] == 1 or x[1] == 2 and data[x[0]][1] <> None and data[x[0]][2] <> None:
            upl = computeupnl(positions[x[0]][0], data[x[0]][1], data[x[0]][2])            
            if upl >= 0:
                mprint(x[0], (len(fieldprint)+3), str(upl)[0:sizefield], color_pair(2))
            else:
                mprint(x[0], (len(fieldprint)+3), str(upl)[0:sizefield], color_pair(1))

        if x[1] == 4:
            storeval(x[2], x[0])

        if x[1] == 8:
            storevol(x[2] - d, x[0])
            update_bollinger(x[0])
            update_fstoc(x[0])
            update_fstocsma(x[0])
            update_rsi(x[0])
            update_adx(x[0])
            strat1(x[0])

        if x[1] == 2:
            ask[x[0]][0] = x[2]

        if x[1] == 1:
            bid[x[0]][0] = x[2]
    
    stdscr.refresh()

    l = time() - lastbar[0]

    if l > barperiod:
        lastbar[0] = time()
        
        for i in range(0,len(contracts)):
            if bars[i][0][1] <> None and bars[i][0][2] <> None and  bars[i][0][3] <> None and  bars[i][0][4] <> None and bars[i][0][5] <> None:
                name = contracts[i].m_symbol
                now = datetime.today().strftime("%Y-%m-%d %H:%M:%S");
                curs.execute("INSERT bars values (%s, %s, %s, %s, %s, %s, %s)", [name, now, bars[i][0][1], bars[i][0][2], bars[i][0][3], bars[i][0][4], bars[i][0][5]])  

        for i in range(0,len(contracts)):
            if strat1position[i] == "WAITING": 
                strat1position[i] == "CLOSED"
                closepos(i)

        for i in range(0,len(contracts)):
            bars[i].insert(0,[None,None,None,None,None,0])
            ask[i].insert(0,None)
            bid[i].insert(0,None)

        stdscr.addstr(len(contracts)+7, 5, "bar index: " + str(len(bars[i])))



    lock.release()

def updatecontractorder(n, cid, p):
    i = 0
    while n <> 0 and i < len(positions[cid][0]):
        
        s = positions[cid][0][i][0]        
        if s * n > 0 :
            i += 1
        else:
            if abs(s) > abs(n):
                positions[cid][0][i][0] = n + s
                n = 0
            else:
                positions[cid][0][i][0] = 0
                n = n + s
                i += 1

    positions[cid][0].append([n,p])    

def order_handler(msg):
    lock.acquire()
    try:

        x = msg.values()
        oid = x[0]

        v = str(x)
        for i in range(0,maxx - len(v)):
            v += " "
            stdscr.addstr(len(contracts)+15, 5, v)


        if orders[oid][2] > 0 and (x[1] == "Cancelled" or x[1] == "Invalid"  or x[1] == "PendingCancel"):                            
            orders[oid][2] = 0
            if strat1position[orders[oid][1]] == "WAITING":
                strat1position[orders[oid][1]] = "CLOSED"
                stdscr.addstr(((orders[oid][1]+1)) + 1, ((len(fieldprint)+6)*sizefield) + namesize, str(strat1position[orders[oid][1]]) + "   ")                    
            position(orders[oid][1])
            pending(orders[oid][1])
            return

        if orders[oid][2] > 0 and x[2] > 0:                            
            if (orders[oid][0].m_action == "BUY"):
                mul = 1
            else:
                mul = -1

            updatecontractorder(mul * x[2], orders[oid][1], x[4])
            # here should print
            gpnl[0] += -(mul * x[2] * x[4])
            printgpnl()
            orders[oid][2] -= x[2]
            date = clock();
            if strat1position[orders[oid][1]] == "WAITING": 
                strat1position[orders[oid][1]] = "OPENED"
                stdscr.addstr(((orders[oid][1]+1)) + 1, ((len(fieldprint)+6)*sizefield) + namesize, str(strat1position[orders[oid][1]]) + "   ")        


    except:

        x = msg.values()
        oid = x[0]

        v = str(x)
        for i in range(0,maxx - len(v)):
            v += " "
            stdscr.addstr(len(contracts)+15, 5, v)

    lock.release()

def error_handler(msg):
    lock.acquire()
    try:
        x = msg.values()
        if x[1] == 202:
            orders[x[0]][2] = 0    

        v = str(x)
        for i in range(0,maxx - len(v)):
            v += " "
            stdscr.addstr(len(contracts)+16, 5, v)
    except:
        v = str(x)
        for i in range(0,maxx - len(v)):
            v += " "
            stdscr.addstr(len(contracts)+16, 5, v)

    lock.release()

def buildgraph(cid):
    left, width = 0.1, 0.9

    rect1 = [left, 0.01, width, 0.4]
    rect2 = [left, 0.45, width, 0.1]
    rect3 = [left, 0.60, width, 0.1]
    rect4 = [left, 0.75, width, 0.1]
    rect5 = [left, 0.90, width, 0.1]

    fig = figure()

    axescolor  = '#f6f6f6'

    ax = fig.add_axes(rect1, axisbg=axescolor)  #left, bottom, width, height
    ax2 = fig.add_axes(rect2, axisbg=axescolor, sharex=ax)
    ax3 = fig.add_axes(rect3, axisbg=axescolor, sharex=ax)
    ax4 = fig.add_axes(rect4, axisbg=axescolor, sharex=ax)
    ax5 = fig.add_axes(rect5, axisbg=axescolor, sharex=ax)

    # ax = fig.add_subplot(111)            

    # candle stick
    M = []
    for i in bars[cid]:
        if i[0] != None and i[1] != None and i[2] != None and i[3] != None and i[4] != None and i[5] != None:
            M.insert(0, (i[0], i[1], i[4], i[2], i[3], i[5]))
            
    candlestick(ax, M, width=0.6)

    # bollinger middle
    M = []
    for i in bollinger_middle[cid]:
        M.insert(0, i)
    date=range(N,N+len(M))
    ax.plot(date, M)

    # upper and lower band
    M1 = []
    M2 = []
    for i in range(0, len(bollinger_stddev[cid])):
        M1.insert(0, bollinger_middle[cid][i] + (K * bollinger_stddev[cid][i]))
        M2.insert(0, bollinger_middle[cid][i] - (K * bollinger_stddev[cid][i]))
    date=range(2*N,2*N+len(M1))            
    ax.plot(date, M1)
    ax.plot(date, M2)


    # ax2 = fig.add_subplot(111)            

    # fstoc
    M = []
    for i in fstoc[cid]:
        M.insert(0, i)
    date=range(KN,KN+len(M))
    ax2.plot(date, M)

    # fstoc sma
    M = []
    for i in fstocsma[cid]:
        M.insert(0, i)
    date=range(KN+Nfstoc,KN+Nfstoc+len(M))
    ax2.plot(date, M)

    # bid
    #M = []
    #for i in bid[cid]:
    #    M.insert(0, i)
    #date=range(1,len(M)+1)
    #ax.plot(date, M)

    # ask
    #M = []
    #for i in ask[cid]:
    #    M.insert(0, i)
    #date=range(1,len(M)+1)
    #ax.plot(date, M)

    # RSI
    M = []
    for i in RSI[cid]:
        M.insert(0, i)
    date=range(RSIN,len(M)+RSIN)
    ax4.plot(date, M)

    # ADX
    #M = []
    #for i in ADX[cid]:
    #    M.insert(0, i)
    #date=range(ADXN,len(M)+ADXN)
    #ax3.plot(date, M)

    # ADX2
    M = []
    for i in ADX2[cid]:
        M.insert(0, i)
    date=range(ADXN,len(M)+ADXN)
    ax3.plot(date, M)

    # std
    M = []
    for i in stdk[cid]:
        M.insert(0, i)
    date=range(2*N,len(M)+2*N)
    ax5.plot(date, M)

    #ax.autoscale_view()
    #ax2.autoscale_view()
    #ax3.autoscale_view()
    #ax4.autoscale_view()
    #ax5.autoscale_view()

    now = datetime.today().strftime("-%Y-%m-%d-%H-%M-%S");
    textsize = 12
    #fig.text(0.025, 1, now, va='top', transform=ax3.transAxes, fontsize=textsize)

    fig.text(0.1, 0.03, "quote", va='top', transform=ax3.transAxes, fontsize=textsize)
    fig.text(0.1, 0.47, "fast stoch.", va='top', transform=ax3.transAxes, fontsize=textsize)
    fig.text(0.1, 0.62, "ADX2", va='top', transform=ax3.transAxes, fontsize=textsize)
    fig.text(0.1, 0.77, "RSI", va='top', transform=ax3.transAxes, fontsize=textsize)
    fig.text(0.1, 0.92, "Stdev", va='top', transform=ax3.transAxes, fontsize=textsize)

    #rect1 = [left, 0.01, width, 0.4]
    #rect2 = [left, 0.45, width, 0.1]
    #rect3 = [left, 0.60, width, 0.1]
    #rect4 = [left, 0.75, width, 0.1]
    #rect5 = [left, 0.90, width, 0.1]

    # volume
    filename = "./charts/" + contracts[cid].m_symbol + now + ".png"
    fig.savefig(filename)


if __name__ == '__main__':

# init curse
    stdscr = initscr()
    start_color()
    noecho()
    cbreak()
    stdscr.keypad(1)

    (maxy, maxx) = stdscr.getmaxyx()

    init_pair(1, COLOR_RED, COLOR_BLACK)
    init_pair(2, COLOR_GREEN, COLOR_BLACK)
    init_pair(3, COLOR_WHITE, COLOR_BLACK)

# just a sleep to be sure everything is well initialized
    sleep(1)

# printing columns
    for i in (fieldprint):
        stdscr.addstr(0, (i*sizefield) + namesize, fieldname[i])        

    stdscr.addstr(0, (curfield*sizefield) + namesize, fieldname[fieldprint[curfield]], A_REVERSE)        

    stdscr.addstr(0, (len(fieldprint)*sizefield) + namesize, "contract details")        

    stdscr.addstr(0, ((len(fieldprint)+3)*sizefield) + namesize, "Unreal. P&L")        

    stdscr.addstr(0, ((len(fieldprint)+4)*sizefield) + namesize, "Position")        

    stdscr.addstr(0, ((len(fieldprint)+5)*sizefield) + namesize, "Pending")        

    stdscr.addstr(0, ((len(fieldprint)+6)*sizefield) + namesize, "strat")        

    stdscr.addstr(0, ((len(fieldprint)+7)*sizefield) + namesize, "stddev")        

    conn = MySQLdb.connect(host='localhost', db='finance', user='finance', passwd='lekiller')
    curs = conn.cursor()

# connection to TWS + branching the tickSize/TickPrice messages
    con = ibConnection()
    con.register(tick_handler, message.TickSize)
    con.register(tick_handler, message.TickPrice)
    con.register(order_handler, message.OrderStatus)
    con.connect()


# add stocks to check

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

    for i in stocks:
        addstock(i[0], i[1], i[2])

# add indexes to check

#    indexes = [("SPX","CBOE"), 
#               ("N225","OSE.JPN"),
#               ("TOPX","TSE.JPN"),
#               ("CAC40","MONEP"),
#               ("DAX", "DTB"),
#               ("NDX", "NASDAQ"),
#               ("DJX", "CBOE"),
#             ]

#    for i in indexes:
#        addindex(i[0], i[1])

# add futurs to check

#    futurs = [("DAX","DTB","20090918")]

#    for i in futurs:
#        addfutur(i[0], i[1], i[2])
        
# add options to check

#    options = [("GS","CBOE","20091016", 90, "PUT")]

#    for i in options:
#        addoption(i[0], i[1], i[2], i[3], i[4])


# -------------------

    stdscr.addstr(2, 0, contracts[0].m_symbol, A_REVERSE)

    printgpnl()

    lastbar[0] = time()

    stdscr.addstr(len(contracts)+7, 5, "bar index: " + str(len(bars[0])))

# building different contract (and printing their symbol for once)

    con.register(error_handler, message.Error)


# waiting the key 'q'
    
    while 1:
        c = stdscr.getch()
        if c == ord('q'): break  # Exit the while()
        elif c == KEY_DOWN:
            if curcontract + 1 < len(contracts):
                stdscr.addstr(((curcontract+1)) + 1, 0, contracts[curcontract].m_symbol)
                curcontract += 1
                stdscr.addstr((curcontract+1) +1, 0, contracts[curcontract].m_symbol, A_REVERSE)
        elif c == KEY_UP:
            if curcontract > 0:
                stdscr.addstr((curcontract+1) +1, 0, contracts[curcontract].m_symbol)
                curcontract -= 1
                stdscr.addstr((curcontract+1) +1, 0, contracts[curcontract].m_symbol, A_REVERSE)
        elif c == KEY_LEFT:
            if curfield > 0:
                stdscr.addstr(0, (curfield*sizefield) + namesize, fieldname[fieldprint[curfield]])
                curfield -= 1
                stdscr.addstr(0, (curfield*sizefield) + namesize, fieldname[fieldprint[curfield]], A_REVERSE)
        elif c == KEY_RIGHT:
            if curfield + 1 < len(fieldprint):
                stdscr.addstr(0, (curfield*sizefield) + namesize, fieldname[fieldprint[curfield]])
                curfield += 1
                stdscr.addstr(0, (curfield*sizefield) + namesize, fieldname[fieldprint[curfield]], A_REVERSE)
        elif c == ord('a'):
            # buy mkt
            addmktorder(curcontract, 'BUY', 100)
        elif c == ord('s'):
            # sell mkt
            addmktorder(curcontract, 'SELL', 100)
        elif c == ord('z'):            
            if len(fstoc[curcontract]) > 0 and len(fstocsma[curcontract]) > 0 and len(bollinger_middle[curcontract]) > 0 and len(bollinger_stddev[curcontract]) > 0 and bars[curcontract][0][4] != None:
                price = float(bollinger_middle[curcontract][0] - (2 * bollinger_stddev[curcontract][0]))
                stdscr.addstr(56, 5, str(price))
                addlmtorder(curcontract, 'BUY', price, 100)
        elif c == ord('x'):
            if len(fstoc[curcontract]) > 0 and len(fstocsma[curcontract]) > 0 and len(bollinger_middle[curcontract]) > 0 and len(bollinger_stddev[curcontract]) > 0 and bars[curcontract][0][4] != None:
                addlmtorder(curcontract, 'SELL', bollinger_middle[curcontract][0] + (K * bollinger_stddev[curcontract][0]), 100)
        elif c == ord('c'):
            closepos(curcontract)
        elif c == ord('w'):
            if strat1position[curcontract] == "CLOSED": strat1position[curcontract] = "STOPPED"
            elif strat1position[curcontract] == "STOPPED": strat1position[curcontract] = "CLOSED"
            elif strat1position[curcontract] == "OPENED": 
                strat1position[curcontract] = "CLOSED"
                closepos(curcontract)
            stdscr.addstr(((curcontract+1)) + 1, ((len(fieldprint)+6)*sizefield) + namesize, str(strat1position[curcontract]) + "   ")        
        elif c == ord('g'):
            buildgraph(curcontract)
        elif c == ord('f'):
            for i in range(0, len(contracts)):
                buildgraph(i)
        elif c == ord('h'):

            M = bars[curcontract]
            stdscr.addstr(len(contracts)+15, 5, str(M))

            M = bollinger_middle[curcontract]
            stdscr.addstr(len(contracts)+20, 5, str(M))

            M = bollinger_stddev[curcontract]
            stdscr.addstr(len(contracts)+25, 5, str(M))

            M = fstoc[curcontract]
            stdscr.addstr(len(contracts)+30, 5, str(M))

        elif c == ord('v'):
            #price = bars[curcontract][0][4]
            #if (price != None):
            #    stdscr.addstr(57, 5, str(price))            
            addlmtorder(curcontract, 'BUY', 100.0, 100)            
            

# unsetting curse and exiting

    nocbreak(); stdscr.keypad(0); echo()
    endwin()
