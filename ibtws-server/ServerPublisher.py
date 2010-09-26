# for pyro
import Pyro.core
import Pyro.naming
import Pyro.constants
import Pyro.EventService.Clients

# the object to notice event

fieldname = ["BID", "BID", "ASK", "ASK", "LAST", "LAST", "HIGH", "LOW", "VOLUME", "CLOSE"]

class ServerPublisher(Pyro.EventService.Clients.Publisher):
    def __init__(self):
        Pyro.EventService.Clients.Publisher.__init__(self)
