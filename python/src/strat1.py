from contract import *
from threading import *
from time import *
from math import *
from datetime import *

class Strat1(Thread):

    def __init__(self, stck, N, kdown, kup, pose, risk):
        self.c = Stock(stck)
        self.state = "CLOSED"
        self.data = []
        Thread.__init__(self)
        self.daemon = True

        # strat param
        self.N = N
        self.kdown = kdown
        self.kup = kup
        self.pose = pose
        self.risk = risk

        self.timeout = timedelta(seconds=10)

    def __del__(self):
       pass 

    def run(self):

        sleep(5)
        while True:

            sleep(1)
            # first the new data
            newdata = dict()
            newbar = self.c["rtbar"]

            #we put the close
            #try:
            #    newdata["close"] = newbar[5]
            #except:
            #    newdata["close"] = self.c["mktdata"]["LAST PRICE"]

            newdata["close"] = self.c["mktdata"]["LAST PRICE"]

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
            try:
                if self.state == "CLOSED" and newdata["k"] < self.kdown:
                    self.state = "OPENING"
                    self.c.order(orderty = "LMT", quantity = int(self.pose / newdata["close"]))
                    openingtime = datetime.now()
                    print "CLOSED --> OPENING"
            except Exception as inst:
                print inst
                self.state = "CLOSED"
                pass
            
            # if we are opening, and that the position is > 0, it means that we are open
            if self.state == "OPENING" and self.c["position"] > 0:
                self.state = "OPENED"
                print "OPENING --> OPENED"
                
            # if we hit the timeout, cancel it and retry
            if self.state == "OPENING" and (openingtime + self.timeout) < datetime.now():
                self.c.cancel()
                self.c.order(orderty = "LMT", quantity = int(self.pose / newdata["close"]))
                openingtime = datetime.now()
                print "OPENING --> OPENING (time out)"

            # if we are opened, we leave if: 1) we are > kup, 2) we loose risk% of our pose 
            if self.state == "OPENED":
                    
                if newdata["k"] > self.kup and self.c["upnl"] > 0:
                    self.state = "CLOSING"
                    self.c.close(orderty = "LMT")
                    closingtime = datetime.now()
                    print "OPENED --> CLOSING (stopgain)"

                elif self.c["upnl"] - self.c["pnl"] < self.risk * self.pose:
                    self.state = "CLOSING"
                    self.c.close(orderty = "LMT")
                    closingtime = datetime.now()
                    print "OPENED --> CLOSING (stoploss)"

            if self.state == "CLOSING" and self.c["position"] == 0:
                self.pose += self.c["pnl"]
                self.state = "CLOSED"
                print "CLOSING --> CLOSED (pose = " + str(self.pose) + ")"

            if self.state == "CLOSING" and closingtime + self.timeout < datetime.now():
                self.c.cancel()
                self.c.close(orderty = "LMT")
                closingtime = datetime.now()                
                print "CLOSING --> CLOSING (timeout)"
                
            # finally we insert the newdata
            self.data.insert(0, newdata)

            # we remove elements in the list as they are not needed
            if len(self.data) > self.N:
                self.data.pop()
