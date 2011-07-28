from sets import *

from threading import *

from pickle import *

class SpreadSheet:

  def __init__(self, _globals = None, callback = None, file = None):
    if _globals == None:
      self._globals = globals()
    else:
      self._globals = _globals

    self._debug = False

    self.glock = Lock()

    self.recomputing = False

    #callback:: action -> param -> ()
    # action == "update" -> param == (key, value)
    # action == "delete" -> param == key
    
    self.callback = callback

    # contains 
    # (formula::String, value::Object,)
    # if fromula is None then it's direclt a value
    self._cells = {}

    # dep: downside dependency
    # a dict of key::String to set of keys
    # k -> {k1, k2, k3} means that the value of k is used in the computation of k1, k2, k3
    self._dep = {}

    # stack of currently evaluating cells
    self._dep_stack = []

    if file <> None:
      self.load(file)



  def __str__(self):
    res = "-------------------------------------------------\n"

    for i in self._cells:      
      res += i 
      formula = self.getformula(i)
      if formula <> None:
        res += " ::= " + formula[1:]

      res += " = " + str(self[i]) + "\n"
      
    for i in self._dep:
      res += i +" is used in : " 

      for j in self._dep[i]:
        res += j + ", "

      res += "\n"  

    res += "--------------------------------------------------------\n"

    return res


  # this is a frontend version for __setitem__
  # this one is locked. All thread changing a cell value should use this function
  # block = False means that if the lock is taken we are getting out directly
  def setformula(self, key, formula, blocking = True):
    
    if not blocking and self.glock.locked():
      return None    
    
    self.glock.acquire()
    self[key] = formula
    res = self[key]
    self.glock.release()    
    return res

  # front end for recomputation
  def recompute(self, key, blocking = True):

    if not blocking and self.glock.locked():
      return None    

    self.glock.acquire()

    formula = self.getformula(key)
    self[key] = formula
    res = self[key]
    self.glock.release()    
    return res


  # this computes the list of sets of elements that needs to be recomputed
  def compute_recompute(self, key):
    return self.compute_recomputes([key])

  def compute_recomputes(self, keys):
    # the result will be a list of sets
    res = []
    # current_sets of recomputation
    current_set = Set()
    for i in keys:
      current_set.update(self._dep[i])
    # while there is dependencies
    while len(current_set) > 0:
      # we initialize the next set
      next_set = Set()
      # adding all following dependencies
      for i in current_set:
        next_set.update(self._dep[i])
      # we save the current_set by appending it in the res
      res.append(current_set)
      # and the current_set is the next one
      current_set = next_set

    # here we are sure that current_set = Set(), and that we are done

    # reverse traversing the list of sets, with i
    resi = range(0, len(res))
    resi.reverse()
    for i in resi:
      # we remove all the elements from the current set from the others
      for j in range(0, i):
        res[j] -= res[i]

    # finally we return res
    return res
    

  # remove the key as dependent from other key
  def remove_key_dependency(self, key):
    for i in self._dep:
      self._dep[i].discard(key)    

  # remove a key
  def remove_key(self, key):
    
    self.glock.acquire()
    try:
      del self._cells[key]
      self.recompute_dependency(key)
      del self._dep[key]
      if self.callback <> None:
        self.callback("delete", key)
    except Exception as e:
      print "error := " + str(e)
      pass
    self.glock.release()    

  # set a formula
  def setformula(self, key, formula):
    try:
      self._cells[key] = (formula[1:], eval(formula[1:], self._globals, self))
    except Exception as e:
      self._cells[key] = (formula[1:], str(e))

  # setting a cell
  def setcell(self, key, formula):
    # then we push the key in the dependency stack
    self._dep_stack.append(key)

    # here we change the formula of the cell
    # and thus recompute it
    if isinstance(formula, str) and len(formula) > 0 and formula[0] == '=':
      self.setformula(key, formula)
    else:
      self._cells[key] = (None, formula)

    # calling call back
    if self.callback <> None:
      self.callback("update", (key, self._cells[key][1]))

    if self._debug:
      print "self.__setitem__(" + key + ", " + str(formula) + ") = " + str(self.getvalue(key))

    # we pop the key in the dependency stack
    self._dep_stack.pop()

  # recompute the key dependency
  def recompute_dependency(self, key):

    if self._debug:
      print "self.recompute_dependency(" + key + ")"

    self.recomputing = True

    # we "neutralize" the dependency stack
    l = self._dep_stack
    self._dep_stack = []

    recomputesets = self.compute_recompute(key)

    if self._debug:
      print "recomputesets := " + str(recomputesets)

    # recompute all dependencies
    for i in recomputesets:
        for j in i:
          # grab the formula, and if it exist then recompute cell value
          f = self.getformula(j)
          if f != None:
            self[j] = f
          if self._debug:
            print "recomputing " + j + " = " + str(self.getvalue(j))



    # restore the dependency stack
    self._dep_stack = l

    self.recomputing = False


  # we are setting a value
  def __setitem__(self, key, formula):

    # first, as we change the formula of the cell
    # we remove its dependency to other cell
    self.remove_key_dependency(key)

    # we store the previous value
    try:
      old_val = self.getvalue(key)
    except:
      pass

    # if I am not registered in _dep I do so
    if key not in self._dep:
      self._dep[key] = Set()

    # we set the cell
    self.setcell(key, formula)

    # we only recompute if we have a different value
    # or if we are not recomputing
    try:
      if self.recomputing or self.getvalue(key) == old_val:
        return
    except:
      pass

    # than we recompute all dependencies
    # TODO: compute better dependencies to avoid recompute several time the same var
    # DONE
    self.recompute_dependency(key)

  def getformula(self, key):
    # we get the entry for the key
    try:
      c = self._cells[key]
    except:
      return None

    # and just return the first projection
    if c[0] == None:
      return None
    else:
      return "=" + c[0]


  def __getitem__(self, key):
    if self._debug:
      print "self.__getitem__(" + key + ")"      

    # look if the evaluation comes from another cell computation
    if len(self._dep_stack) > 0:
      # yes, so we are a dependency to another cell
      #self._dep[key].add(self._dep_stack[len(self._dep_stack)-1])
      self._dep[key].update(Set(self._dep_stack))
      #self._dep[key] = (Set(self._dep_stack))

    # and just return the second projection
    return self.getvalue(key)

  def getvalue(self, key):
    return self._cells[key][1]

  # here a bunch of function with special "semantics"
  def ifte(self):
      print "ifte"
      def ifte_core(cond, true, false):
          if cond:
              return true(self)
          else:
              return false(self)
      return ifte_core

  def myself(self):
      print "myself"
      return self

  def save(self, file):
    # dump the cells
    dump((self._cells, self._dep), file, 1)

  def load(self, file):
    for i in self._cells.keys():
      self.remove_key(i)

    (self._cells, self._dep) = load(file)
    
    if self.callback <> None:
      for key in self._cells:
        self.callback("update", (key, self._cells[key][1]))
      



if __name__ == '__main__':
  from math import sin, pi
  
  from spreadsheet import *
  
  ss = SpreadSheet()
  
  ss._globals = globals()
  ss._globals.update(locals())
  
  ss['a1'] = 5
  ss['a2'] = '=a1*6'
  ss['a4'] = '=a1*6'
  ss['a3'] = '=a2*7'
  assert ss['a3'] == 210
  ss['b1'] = '=sin(pi/4)'
  print ss['b1']
  assert ss['b1'] == 0.70710678118654746
  assert ss.getformula('b1') == '=sin(pi/4)'
  print str(ss._cells)
  print str(ss._dep)
  ss['a1'] = 12
  print str(ss._cells)
  print str(ss._dep)

  #--------------------------------------------------------

  ss2 = SpreadSheet()

  ss2['a1'] = 12
  ss2["a2"] = "=a1+1"
  ss2["a3"] = "=a1+2"
  ss2["a4"] = "=a2+a3"
  
  print ss2
  
  ss2._debug = False
  
  ss2["a1"] = 0

  #--------------------------------------------------------

  ss3 = SpreadSheet()

  print "-----------------------------------------------------"
  ss3._debug = False
  
  ss3["b"] = True
  
  ss3["prec"] = 10
  
  ss3["a"] = "=prec + 1"
  ss3["c"] = 2
  
  def f(val):
    print val
    return val
  
  ss3._globals.update(locals())
  
  ss3["test"] = "= f(a + prec) if b else f(c)"

  ss3["d"] = "=test + 2"
  
  print ss3
  print "-----------------------------------------------------"
  
  ss3["c"] = 3
  
  print ss3
  print "-----------------------------------------------------"
  ss3["b"] = False
  
  print ss3
  print "-----------------------------------------------------"

  #--------------------------------------------------------

  ss4 = SpreadSheet()
  ss4._debug = False

  ss4['A1'] = True
  ss4['B1'] = False
  ss4['C1'] = "=A1 and B1"

  ss4.remove_key("B1")

  print ss4
  
  print "save"
  ss4.save(open('ss4.pkl', 'wb'))

  ss5 = SpreadSheet(file = open('ss4.pkl', 'rb'))

  print ss5

  ss6 = SpreadSheet(file = open('ss.pkl', 'rb'))

  print ss6
