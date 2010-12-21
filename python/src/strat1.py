from contract import *
from threading import *
from time import *
from math import *
from datetime import *

class Strat1(Thread):

    # params = [stck, N, kdown, kup, pose, risk, ordertimout, barsize]
    def __init__(self, params):

        self.c = Stock(params[0])
        self.state = "CLOSED"
        self.data = []

        Thread.__init__(self)

        self.daemon = True

        # strat param
        self.N = params[1]
        self.kdown = params[2]
        self.kup = params[3]
        self.originpose = float(params[4])
        self.pose = float(params[4])
        self.risk = float(params[5])

        self.ordertimeout = timedelta(seconds=params[6])
        self.barsize = timedelta(seconds=params[7])

        self.opened = True

    def __del__(self):
       pass 

    def open(self):
        self.restart()
        self.opened = True
        self.start()


    def close(self):
        self.c.stop()
        self.opened = False
        self.state = "CLOSED"
        sleep(2)

    def run(self):

        print "Start"

        # first the new data
        newdata = dict()

        val = self.c["mktdata"]["LAST PRICE"]

        while val == None:
            val = self.c["mktdata"]["LAST PRICE"]

        newdata["open"] = newdata["high"] = newdata["low"] = newdata["close"] = val
        newdata["start"] = datetime.now()

        while self.opened:
          
            #update the OHLCV
            
            newdata["close"] = self.c["mktdata"]["LAST PRICE"]
            if newdata["close"] > newdata["high"]:
                newdata["high"] = newdata["close"]

            if newdata["close"] < newdata["low"]:
                newdata["low"] = newdata["close"]


            # first compute the mean (ema on N)
            try:
                alpha = 2.0/(self.N+1)
                newdata["mean"] = newdata["close"] * alpha + (1 - alpha) * self.data[0]["mean"]
            except Exception as inst:
                newdata["mean"] = newdata["close"]

            # then we compute the sigma, between 
            msum = 0
            try:

                for i in range(0,self.N-1):
                    msum += (self.data[i]["close"] - self.data[i]["mean"])**2
            except:
                pass

            msum += (newdata["close"] - newdata["mean"])**2
            
            msum = sqrt(msum)

            newdata["stdev"] = msum

            # we compute the current k
            try:
                newdata["k"] = (newdata["close"] - newdata["mean"])/newdata["stdev"]
            except:
                newdata["k"] = 0
    
            # if we are closed and the price number of sigma is < kdown we buy
            # only if enough bars are here
            if len(self.data) > self.N-1: 

                try:
                    if self.state == "CLOSED" and newdata["k"] < self.kdown:
                        self.state = "OPENING"
                        openorder = self.c.order(orderty = "LMT", quantity = int(self.pose / newdata["close"]))
                        openingtime = datetime.now()
                        opentry = 0
                        #print "CLOSED --> OPENING"
                except Exception as inst:
                    print "err in transition opening: " + str(inst)
                    print newdata
                    print (newdata["k"], newdata["close"])
                    self.state = "CLOSED"
                    pass
            
                # if we are opening, and that the position is > 0, it means that we are open
                if self.state == "OPENING" and self.c["position"] > 0:
                    self.state = "OPENED"                    
                    #print "OPENING --> OPENED"
                
                # if we hit the timeout, cancel it and retry
                if self.state == "OPENING" and (openingtime + self.ordertimeout) < datetime.now():
                    self.c.cancel()
                    openorder = self.c.order(orderty = "LMT", quantity = int(self.pose / newdata["close"]))
                    openingtime = datetime.now()
                    opentry += 1
                    if opentry < 5:
                        #print "OPENING --> OPENING (time out)"
                        pass
                    else:
                        self.state = "CLOSED"
                        #print "OPENING --> CLOSED (time out)"

                # if we are opened, we leave if: 1) we are > kup, 2) we loose risk% of our pose 
                if self.state == "OPENED":
                    
                    if newdata["k"] > self.kup and self.c["upnl"] > 0:
                        self.state = "CLOSING"
                        closeorder = self.c.close(orderty = "LMT")
                        closingtime = datetime.now()
                        #print "OPENED --> CLOSING (stopgain)"

                    elif self.c["upnl"] < -(self.risk * self.pose):
                        self.state = "CLOSING"
                        closeorder = self.c.close(orderty = "LMT")
                        closingtime = datetime.now()
                        #print "OPENED --> CLOSING (stoploss: " + str(self.c["upnl"]) + " < " + str(- (self.risk * self.pose)) + ")"

                if self.state == "CLOSING" and self.c["position"] == 0:
                    self.state = "CLOSED"
                    self.pose = self.originpose + self.c["rpnl"]
                    #print "CLOSING --> CLOSED (pose = " + str(self.pose) + ")"

                if self.state == "CLOSING" and closingtime + self.ordertimeout < datetime.now():
                    self.c.cancel()
                    closeorder = self.c.close(orderty = "LMT")
                    closingtime = datetime.now()                
                    #print "CLOSING --> CLOSING (timeout)"

            # finally we insert the newdata if the bar size is reached
            if datetime.now() > newdata["start"] + self.barsize:

                #print newdata
                
                self.data.insert(0, newdata)

                # we remove elements in the list as they are not needed
                if len(self.data) > self.N:
                    self.data.pop()
                    self.c.pop()

                # we create the new bar
                newdata = dict()
                newdata["open"] = newdata["high"] = newdata["low"] = newdata["close"] = self.c["mktdata"]["LAST PRICE"]
                newdata["start"] = datetime.now()

                # we ask for a new bar in contract
                self.c.newbar()
    
