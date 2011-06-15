from strat1 import *
from time import *

s = Strat1(["MSFT", 10, -0.4, 0.4, 10000, 0.05, 5, 1])

s.start()

while True:
    try:
        pass
        #print s.data[0]
        #print s.state
        #print ""
    except:
        pass
    sleep(5)
