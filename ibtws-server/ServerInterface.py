# for pyro
import Pyro.core
import Pyro.naming
import Pyro.constants
import Pyro.EventService.Clients

# the object exposed through pyro
class ServerInterface(Pyro.core.ObjBase):

        def __init__(self):
                Pyro.core.ObjBase.__init__(self)

	# Exit

        def exit(self):
            os._exit(0)
