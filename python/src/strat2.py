from contract import *
from threading import *
from time import *
from math import *
from datetime import *

from indicators import *

class Strat2(Thread):

    # params = [stck, Nlong, Nshort, pose, risk, ordertimout, barsize]
    def __init__(self, params):

        self.c = Stock(params[0])
        self.state = "CLOSED"
        self.data = []

        Thread.__init__(self)

        self.daemon = True

        # strat param
        self.Nlong = params[1]
        self.Nshort = params[2]
        self.originpose = float(params[3])
        self.pose = float(params[3])
        self.risk = float(params[4])

        self.ordertimeout = timedelta(seconds=params[5])
        self.barsize = timedelta(seconds=params[6])

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

        emaShort = EMAIndicator(self.Nshort, "close")
        emaLong = EMAIndicator(self.Nlong, "close")
        
        entrysig = emaShort.croseup(emaLong)
        exitsig = emaShort.croseup(emaLong)

        while self.opened:

            

            try:
                if self.state == "CLOSED" and entrysig(self.c.bars):
                    self.state = "OPENING"
                    openorder = self.c.order(orderty = "LMT", quantity = int(self.pose / self.c.bars[0]["close"]))
                    openingtime = datetime.now()
                    opentry = 0
            except Exception as inst:
                print "err in transition opening: " + str(inst)
                self.state = "CLOSED"
                pass
            
            # if we are opening, and that the position is > 0, it means that we are open
            if self.state == "OPENING" and self.c["position"] > 0:
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
                    self.state = "CLOSED"

            # if we are opened, we leave if: 1) we are > kup, 2) we loose risk% of our pose 
            if self.state == "OPENED":
                    
                if exitsig(self.c.bars) and self.c["upnl"] > 0:
                    self.state = "CLOSING"
                    closeorder = self.c.close(orderty = "LMT")
                    closingtime = datetime.now()

                elif self.c["upnl"] < -(self.risk * self.pose):
                    self.state = "CLOSING"
                    closeorder = self.c.close(orderty = "LMT")
                    closingtime = datetime.now()

            if self.state == "CLOSING" and self.c["position"] == 0:
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
    
