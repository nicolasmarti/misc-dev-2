from math import sqrt

class TimeSeries:

    data = []

    # constructor
    def __init__(self):
        return(None)

    def __init__(self, data):
        self.data = data
        return(None)
    

    # get/set/add data functions
    def addData(self, d):
        self.data.insert(0, d)
        return(1)

    def setData(self, d):
        if len(self.data) > 0:
            self.data[0] = d
            return(1)
        else:
            return(-1)

    def getData(self):
        return(self.data)

    def __getitem__(self, i):
        return (self.data[i])

    def __setitem__(self, i, y):
        self.data[i] = y

    def length(self):
        return(len(self.data))

    # print
    def str(self):
        return(str(self.data))

    # basic operation on timeseries
    def SMA(self, K, n = 0, f = None):
        try:
            if len(self.data) >= K + n:
                val = 0
                if f == None:
                    for i in range(n, K+n):                
                        val += float(self.data[i])
                else:
                    for i in range(n, K+n):                
                        val += float(f(self.data[i]))
                val /= float(K)
                return(val)
            return(None)
        except: 
            return(None)

    def EMA(self, K, n = 0, f = None):
        try:
            alpha = 2.0/(K+1.0)
            if len(self.data) >= K + n:
                val = 0
                it = range(n, K+n)
                it.reverse
                if f == None:
                    for i in it:
                        val = (alpha * float(self.data[i])) + ((1-alpha) * val)
                else:
                    for i in it:
                        val = (alpha * float(f(self.data[i]))) + ((1-alpha) * val)
                return(val)
            return(None)
        except:
            return(None)

    def stdev(self, K, n = 0, f = None):
        try:
            if len(self.data) >= K + n:
                mu = self.SMA(K, n, f)
                val = 0
                if f == None:
                    for i in range(n, K+n):
                        val += (mu - float(self.data[i]))**2
                else:
                    for i in range(n, K+n):
                        val += (mu - float(f(self.data[i])))**2
                val /= K
                val = sqrt(val)
                return(val)
            return(None)
        except:
            return(None)

    # map
    def tsmap(self, f):
        data = map(f, self.data)
        return(TimeSeries(data))

    # fold
    def tsfold(self, f, a):
        try:
            val = a
            for i in self.data:
                val = f(a, val)        
            return(val)
        except:
            return(None)

    
            
    
