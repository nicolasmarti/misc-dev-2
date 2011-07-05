from contract import *
from threading import *
from time import *
from math import *
from datetime import *

from indicators import *

class Automaton(Thread):

    # params = [stck, Nlong, Nshort, pose, risk, ordertimout, barsize]
    def __init__(self, strat, contract):

        ###############################################

        # strat is a dictionnary that contains:
        # TOTHINK: should it be better to have an object ???

        # function init(strat :: dict, contract :: contract, money :: dict) :: Bool
        # this function is called at initialization of the automaton loop for the strategy to initialize itself (record params in itself)
        # returns a boolean asserting if the automaton loop should be started

        # function step(strat :: dict, contract :: contract, money :: dict) :: ()
        # this function is called at the begining of the loop of the automaton
        # this is responsible for updating the contract data, ...

        # function entry(strat :: dict, contract :: contract, money :: dict) :: Bool
        # this function is called each at each iteration of the automaton loop when the state is CLOSED
        # if it returns True, it means it has (by side-effect) proceed an order on the contract

        # function exit(strat :: dict, contract :: contract, money :: dict) :: Bool
        # this function is called each at each iteration of the automaton loop when the state is OPENED
        # if it returns True, it means it has (by side-effect) to close the current position

        # timedelta opentimeout: the timeout for opening
        # timedelta closetimeout: the timeout for closing

        # it should also contains data for money management

        ###############################################

        # contract is an IBContract object

        ###############################################                

        self.state = "CLOSED"

        Thread.__init__(self)
        self.daemon = True

        self.opened = True

        self.contract = contract
        self.strat = strat

    def __del__(self):
       pass 

    def stop(self):
        self.opened = False
        sleep(2)

    def run(self):

        print "automaton start"

        # initialization of the strategy
        self.opened = self.strat["init"](self.strat, self.contract)

        while self.opened:

            # update for the strategy
            self.strat["step"](self.strat, self.contract)

            # we are closed, let's see what the strategy is telling us
            try:
                if self.state == "CLOSED" and self.strat["entry"](self.strat, self.contract):
                    self.state = "OPENING"
                    print "CLOSED -> OPENING"
                    openingtime = datetime.now()
            except Exception as inst:
                print "err in transition opening: " + str(inst)
                self.state = "CLOSED"
                pass
            
            # if we are opening, and that the position is > 0, it means that we are open
            if self.state == "OPENING" and self.c["position"] > 0:
                print "OPENING -> OPENED"
                self.state = "OPENED"                    
                
            # if we hit the timeout, cancel it and set to CLOSED
            if self.state == "OPENING" and (openingtime + self.ordertimeout) < datetime.now():
                self.contract.cancel()
                print "OPENING -> CLOSED"
                self.state = "CLOSED"

            # if we are opened, we leave if the strategy says so
            if self.state == "OPENED":
                    
                if self.strat["exit"](self.strat, self.contract):
                    print "OPENED -> CLOSING"
                    self.state = "CLOSING"
                    closingtime = datetime.now()

            # if we are closing and our position is null, then we are closed
            if self.state == "CLOSING" and self.contract["position"] == 0:
                print "CLOSING -> CLOSED"
                self.state = "CLOSED"

            # if we are closing and the timeout has passed, we force closing
            if self.state == "CLOSING" and closingtime + self.ordertimeout < datetime.now():
                self.contract.cancel()
                closeorder = self.contract.close(orderty = "LMT")
                closingtime = datetime.now()                

        print "automaton stop"
