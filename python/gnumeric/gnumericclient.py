import Pyro.core
import time
from datetime import datetime
from random import *

from Pyro.EventService.Clients import Subscriber

o = Pyro.core.getProxyForURI("PYRONAME://GnumericInterface")

print o.setCell(0,0, (0,0), "=1+A2")
print o.setCell(0,0, (0,1), "=1+8")

while True:
    time.sleep(1)
    dt = datetime.now()
    print o.setCell(0,0, (0,0), str(dt))
    for i in range(1, 10):
        print o.setCell(0,0, (0,i), "=" + str(random()))
