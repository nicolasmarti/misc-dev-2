# for pyro
import Pyro.core
import Pyro.naming
import Pyro.constants
import Pyro.EventService.Clients

# the object exposed through pyro
class ServerInterface(Pyro.core.ObjBase):

    def __init__(self, con):
        Pyro.core.ObjBase.__init__(self)
        self.m_con = con

    # account information
    def accountStatus(self, flag):
        self.m_con.reqAccountUpdates(flag, '')

    # Exit

    def exit(self):
        os._exit(0)
