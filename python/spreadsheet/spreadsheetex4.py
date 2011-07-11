print "(1)"

def printandreturn(val):
    print val
    return val

print "(2)"
f = lambda _: printandreturn(0+5)

print "(3)"
lambda _ : f(None)
