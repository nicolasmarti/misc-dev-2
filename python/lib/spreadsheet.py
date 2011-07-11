from sets import *

from threading import *

class SpreadSheet:

  # contains 
  # (formula::String, value::Object,)
  # if fromula is None then it's direclt a value
  _cells = {}

  # dep: downside dependency
  # a dict of key::String to set of keys
  # k -> {k1, k2, k3} means that the value of k is used in the computation of k1, k2, k3
  _dep = {}

  # stack of currently evaluating cells
  _dep_stack = []

  def __init__(self, _globals = None):
    if _globals == None:
      self._globals = globals()
    else:
      self._globals = _globals

    self._debug = False

    self.glock = Lock()


    # initialize "special" functions
    self.specials = dict()
    self.specials["ifte"] = self.ifte
    self.specials["self"] = self.myself

    pass


  def __str__(self):
    res = ""

    for i in self._cells:      
      res += i 
      formula = self.getformula(i)
      if formula <> None:
        res += " ::= " + formula[1:]

      res += " = " + str(self[i]) + "\n"

    res += str(self._dep) + "\n"

    return res


  # this is a frontend version for __setitem__
  # this one is locked. All thread changing a cell value should use this function
  # block = False means that if the lock is taken we are getting out directly
  def setformula(self, key, formula, blocking = True):
    
    if not blocking and self.glock.locked():
      return None    
    
    self.glock.acquire()
    self[key] = formula
    self.glock.release()    
    return self[key]

  # this computes the list of sets of elements that needs to be recomputed
  def compute_recompute(self, key):
    # the result will be a list of sets
    res = []
    # current_sets of recomputation
    current_set = self._dep[key]
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

  # set a formula
  def setformula(self, key, formula):
    try:
      self._cells[key] = (formula[1:], eval(formula[1:], self._globals, self))
    except Exception as e:
      self._cells[j] = (formula[1:], str(e))

  # setting a cell
  def setcell(self, key, formula):
    # then we push the key in the dependency stack
    self._dep_stack.append(key)

    # here we change the formula of the cell
    # and thus recompute it
    if isinstance(formula, str) and formula[0] == '=':
      self.setformula(key, formula)
    else:
      self._cells[key] = (None, formula)

    if self._debug:
      print "self.__setitem__(" + key + ", " + str(formula) + ") = " + str(self.getvalue(key))

    # we pop the key in the dependency stack
    self._dep_stack.pop()

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
    try:
      if self.getvalue(key) == old_val:
        return
    except:
      pass

    # than we recompute all dependencies
    # TODO: compute better dependencies to avoid recompute several time the same var
    # DONE

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

  def getformula(self, key):
    # we get the entry for the key
    c = self._cells[key]
    # and just return the first projection
    if c[0] == None:
      return None
    else:
      return "=" + c[0]


  def __getitem__(self, key):
    if self._debug:
      print "self.__getitem__(" + key + ")"      

    # we first look if it is a special function
    if key in self.specials:        
        # we run the special, that should return a function
        return self.specials[key]()

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
