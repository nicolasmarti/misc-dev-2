from spreadsheet import *

ss = SpreadSheet()

def sma(tser, period):
    try: 
        sum = 0.0
        for i in tser[0:(period-1)]:
            sum += i
        sum /= float(period)
        return sum
    except:
        return None

ss["sma"] = sma

ss["arg1"] = "=None"

ss["arg2"] = "=10"

ss["application"] = "=sma(arg1, arg2)"

print str(ss)

ss["arg1"] = "=range(0, 100)"

print str(ss)
