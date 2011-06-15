from math import *

# the basic class
class Indicator:
    
    def __init__(self):
        pass

    def value(self, bars):
        return None

    def croseup(self, other):
        def value(bars):
            try:
                moldvalue = self.value(bars[1:])
                mnewvalue = self.value(bars)
                otheroldvalue = other.value(bars[1:])
                othernewvalue = other.value(bars)
                return (moldvalue < otheroldvalue) and (mnewvalue > othernewvalue)
            except:
                return False
        return value

    def crosedown(self, other):
        def value(bars):
            try:
                moldvalue = self.value(bars[1:])
                mnewvalue = self.value(bars)
                otheroldvalue = other.value(bars[1:])
                othernewvalue = other.value(bars)
                return (moldvalue > otheroldvalue) and (mnewvalue < othernewvalue)
            except:
                return False
        return value

    def __lt__(self, other):
        def value(bars):
            try:
                myvalue = self.value(bars)
                othervalue = other.value(bars)
                return myvalue < othervalue
            except:
                return False
        return value
    #all the other alike
        

# the lag    
class LagIndicator(Indicator):

    def __init__(self, lag, indicator):
        self.lag = lag
        self.indicator = indicator

    def value(self, bars):
        bars2 = bars[self.lag:]
        self.indicator.value(bars2)

# constant indicator
class CsteIndicator(Indicator):
    def __init__(self, value):
        self.mvalue = value

    def value(self, bars):
        return self.mvalue

# SMA
class SMAIndicator(Indicator):
    def __init__(self, period, label):
        self.period = period
        self.label = label
                
    def value(self, bars):
        bars2 = bars[0:self.period]
        sum = 0
        try:
            for i in bars2:
                sum += i[self.label]
            
            return sum/self.period
        except:
            return None

class EMAIndicator(Indicator):
    def __init__(self, period, label):
        self.period = period
        self.label = label
        self.alpha = 2.0/(float(self.period)+1.0)
 
    def value(self, bars):
        sum = 0.0
        bars2 = bars[0:self.period]
       
        try:
            for i in reversed(bars2):
                sum = sum*(1-alpha) + i[self.label] * alpha
            
            return sum
        except:
            return None

class MuSigEMAIndicator(Indicator):
    def __init__(self, period, label):
        self.period = period
        self.label = label
        self.alpha = 2.0/float(self.period)+1.0
        
    def value(self, bars):
        mu = 0.0        
        stdev = 0.0
        bars2 = bars[0:self.period]
        try:
            for i in reversed(bars2):
                mu = mu*(1-self.alpha) + i[self.label] * self.alpha
                stdev += (mu - i[self.label])**2

            return (mu, sqrt(stdev))
        except Exception as inst:
            print "MuSigEMAIndicator: " + str(inst)
            return None
        
class RSIIndicator(Indicator):
    def __init__(self, period):
        self.period = period
        
    def value(self, bars):
        U = []       
        D = []
        bars2 = bars[0:self.period]
       
        try:
            for i in bars2:
                if i["close"] > i["open"]:
                    U.append({'U' : i["close"] - i["open"]})
                    D.append({'D' : 0})

                if i["close"] <= i["open"]:
                    D.append({'D' : i["open"] - i["close"]})
                    U.append({'U' : 0})

            U.reverse()
            D.reverse()

            Uema = EMAIndicator(self.period, "U")
            Dema = EMAIndicator(self.period, "D")
            RS = Uema.value(U) / Dema.value(D)

            RSI = 100 - 100/(1+RS)
                
            return RSI
        except:
            return None
        
