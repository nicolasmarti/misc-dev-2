from contract import *
from threading import *
from time import *
from math import *
from datetime import *

from indicators import *

class Strat2(Thread):

    # params = [stck, Nlong, Nshort, pose, risk, ordertimout, barsize]
    def __init__(self, params = None, ticker = None):

        if params == None:
            params = dict()
            if ticker == None:
                params["ticker"] = "GS"
            else:
                params["ticker"] = ticker
            params["cash"] = 50000
            params["risk"] = 0.03
            params["timeout"] = 10
            params["barsize"] = 5
            params["N"] = 12
            params["minvol"] = 0.01
            params["kdown"] = -2.0
            params["kup"] = 2.0
            
            

        self.c = Stock(params["ticker"])
        self.state = "CLOSED"
        self.data = []

        Thread.__init__(self)

        self.daemon = True

        # strat param
        self.originpose = float(params["cash"])
        self.pose = float(params["cash"])
        self.risk = float(params["risk"])

        self.ordertimeout = timedelta(seconds=params["timeout"])
        self.barsize = timedelta(seconds=params["barsize"])

        self.params = params

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

        print "run()"

        musig = MuSigEMAIndicator(self.params["N"], "close")
        rsiind = RSIIndicator(self.params["N"])

        while self.opened:

            try:
                bars = self.c.bars

                if len(bars) < self.params["N"]:
                    raise Exception("not yet")
                
                (mu, sig) = musig.value(bars)
                self.musig = (mu, sig)
                rsi = rsiind.value(bars)
                self.rsi = rsi

                self.sig1 = (sig/mu)
                self.sig2 = (self.c.bars[0]["close"] - mu)/sig

                entrysig = ((sig/mu) > self.params["minvol"]) and (self.c.bars[0]["close"] - mu)/sig < self.params["kdown"]
                exitsig = (self.c.bars[0]["close"] - mu)/sig > self.params["kup"]
            except Exception as inst:
                entrysig = False
                exitsig = False

            try:
                if self.state == "CLOSED" and entrysig:
                    self.state = "OPENING"
                    print "CLOSED -> OPENING"
                    openorder = self.c.order(orderty = "LMT", quantity = int(self.pose / self.c.bars[0]["close"]))
                    openingtime = datetime.now()
                    opentry = 0
            except Exception as inst:
                print "err in transition opening: " + str(inst)
                self.state = "CLOSED"
                pass
            
            # if we are opening, and that the position is > 0, it means that we are open
            if self.state == "OPENING" and self.c["position"] > 0:
                print "OPENING -> OPENED"
                self.state = "OPENED"                    
                
            # if we hit the timeout, cancel it and retry
            if self.state == "OPENING" and (openingtime + self.ordertimeout) < datetime.now():
                self.c.cancel()
                openorder = self.c.order(orderty = "LMT", quantity = int(self.pose / self.c.bars[0]["close"]))
                openingtime = datetime.now()
                opentry += 1
                if opentry < 5:
                    pass
                else:
                    print "OPENING -> CLOSED"
                    self.state = "CLOSED"

            # if we are opened, we leave if: 1) we are > kup, 2) we loose risk% of our pose 
            if self.state == "OPENED":
                    
                if exitsig and self.c["upnl"] > 0:
                    print "OPENED -> CLOSING (profit)"
                    self.state = "CLOSING"
                    closeorder = self.c.close(orderty = "LMT")
                    closingtime = datetime.now()

                elif self.c["upnl"] < -(self.risk * self.pose):
                    print "OPENED -> CLOSING (loss)"
                    self.state = "CLOSING"
                    closeorder = self.c.close(orderty = "LMT")
                    closingtime = datetime.now()

            if self.state == "CLOSING" and self.c["position"] == 0:
                print "CLOSING -> CLOSED"
                self.state = "CLOSED"
                self.pose = self.originpose + self.c["rpnl"]

            if self.state == "CLOSING" and closingtime + self.ordertimeout < datetime.now():
                self.c.cancel()
                closeorder = self.c.close(orderty = "LMT")
                closingtime = datetime.now()                

            # finally we insert the newdata if the bar size is reached
            if datetime.now() > self.c.bars[0]["start"] + self.barsize:

                # we ask for a new bar in contract
                self.c.newbar()
    
        print "stop"
