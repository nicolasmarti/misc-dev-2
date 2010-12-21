

# the basic class
class Indicator:
    
    def __init__(self):
        pass

    def value(self, bars):
        return None

    def __lt__(self, other):
        def value(bars):
            myvalue = self.value(bars)
            if myvalue == None: return None
            othervalue = other.value(bars)
            if othervalue == None: return None
            
            return myvalue < othervalue
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


