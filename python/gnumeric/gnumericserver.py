import Gnumeric as g

import thread

import Pyro.core
import Pyro.naming
import Pyro.constants
import Pyro.EventService.Clients

# the object exposed through pyro
class GnumericServer(Pyro.core.ObjBase):

    def __init__(self):
        Pyro.core.ObjBase.__init__(self)


    def setCell(self, wkb, sheet, cellcoo, txt):
        
        wb = g.workbooks()[wkb]
        s = wb.sheets()[sheet]
        c = s[cellcoo[0], cellcoo[1]]
        c.set_text(txt)
        return c.get_value()

    def __del__(self):
        self.daemon.disconnect(self)

Pyro.core.initServer()
ns=Pyro.naming.NameServerLocator().getNS()
daemon=Pyro.core.Daemon()
daemon.useNameServer(ns)
    
si = GnumericServer()
si.daemon = daemon

uri=daemon.connect(si,"GnumericInterface")
print "The daemon runs on port:",daemon.port
print "The object's uri is:",uri

thread.start_new_thread(daemon.requestLoop, ())
