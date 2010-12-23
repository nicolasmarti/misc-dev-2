

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

# EMA
class EMAIndicator(Indicator):
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


