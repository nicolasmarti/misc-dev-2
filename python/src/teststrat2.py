from time import *
from indicators import *
from contract import *

c = Stock("GS")

ema20 = EMAIndicator(20, "close")
ema50 = EMAIndicator(50, "close")

ema20upema50 = ema20.croseup(ema50)
ema50upema20 = ema50.croseup(ema20)

while True:
    sleep(10)

    res1 = ema20upema50(c.bars)
    res2 = ema50upema20(c.bars)

    if res1 <> "None" and res1 == True:
        c.order()

    if res2 <> "None" and res2 == True:
        c.close()

    c.newbar()

    print "res1 = " + str(res1)
    print "res2 = " + str(res2)
    print "position = " + str(c["position"])
    print "upnl = " + str(c["upnl"])
    print "rpnl = " + str(c["rpnl"])
    print "pnl = " + str(c["rpnl"] + c["upnl"])
