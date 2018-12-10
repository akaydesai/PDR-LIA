"""
Module containing all the data structures and for handling formulas.

Prereqs: pip3 install z3-solver #bidict

Doctest: python3 -m doctest formula.py [-v]
"""

from z3 import *  #..bad!
from z3.z3util import get_vars

from collections import Iterable
from functools import reduce
from sys import exit
import itertools
# from bidict import bidict

simplifyAll = lambda l: list(map(simplify, l)) #why not just use Tactic('simplify') ?
"""
Convert an Iterable of formulas into canonical form.
"""
_b_ = Int('b_')
z_true = simplify(_b_==_b_)
z_false = simplify(_b_!=_b_)

class ConjFml(Goal):
  """
  ConjunctiveFormula: Extension of Goal to store and manipulate conjunctive formulas.
  Makes working with formulas for frames, properties and queries easier.
  Use to represent frames, property(P) and !P. 
  IMPORTANT: Assumes that each formula added to it is in CNF. 
  USE ONLY the add method to add formulas. Do not use insert and other methods from parent; those are not overridden, so they do not convert to strict CNF or change flags(safe_varlist).
  
  Converts cnf formula to strict CNF if added using add method.
  For our purposes 'strict' CNF is defined as CNF where no clause has nested non-atomic formulas.
  e.g. Or(x==y,x==1,y==2) is a clause in 'strict' CNF but Or(x==y, Or(x==1,y==2)) is not.

  self.unprimed is a list containing all the variables in the Goal.
  self.primed is the primed version of the same.
  safe_varlist denotes that list of primes and unprimed variables is up to date. 
  If it is set to False, you need to run update_vars.

  #FUTURE TODO: Store clauses in a set, this would allow deletion, musch faster __contains__, but not sure if it'd be true speed up as z3 GoalObj isn't mutable.
  #This would need ConjFml to be it's own class, i.e. not extending Goal.
  """
  def __init__(self):

    # if not isinstance(id, str):
      # raise TypeError("Non-string type id given.")

    super(ConjFml, self).__init__()
    # self._index = -1
    # self.id = id
    self.unprimed = []
    self.primed = []
    self.safe_varlist = True 
    self.solver = Solver()
    self.solver.push()

  def __eq__(self, other):
    """
    Equal iff of same type and have the same clauses. id doesn't matter.

    >>> g = ConjFml()
    >>> f = ConjFml()
    >>> g.add([x == 1, Or(x >= 0, y <= 1), y < 2])
    >>> f.add([y<2, x == 1, Or(x >= 0, y <= 1)])
    >>> g == g
    True
    >>> g == f
    True
    """
    if not isinstance(other, type(self)) and not isinstance(other, type(Goal())):
      raise TypeError("'%s' is not of type '%s' or %s." % (other,type(self),type(Goal())))

    if len(self) != len(other):
      return False
    else:
      return set(self) == set(other)

  def __lt__(self, other):
    """
    Less than method is needed for heappush.
    """
    return len(self) < len(other)

  # def __iter__(self):
  #   """
  #   Let's make ConjFml Iterable. 
  #   This is broken, can't prvide multiple iterators over same object simultaneously.
  
  #   https://stackoverflow.com/questions/46941719/how-can-i-have-multiple-iterators-over-a-single-python-iterable-at-the-same-time
  #   """
  #   self._index = -1
  #   return self
  # def __next__(self):
  #   """
  #   Let's make ConjFml Iterable.
  #   """
  #   self._index += 1
  #   if self._index >= len(self):
  #     self._index = -1
  #     raise StopIteration
  #   return self[self._index]

  def update_vars(self):
    """
    Keep  variable lists up to date to prevent unwanted crap from happening.
    Assumes all vars are unprimed. Do not use on transition system.

    #TODO: Add check for existing prime vars.

    >>> x,y = Ints('x y')
    >>> fml = ConjFml()
    >>> fml.add([x==1,y==2, Or(x>=0, y<=1)])
    >>> fml.unprimed
    []
    >>> fml.primed
    []
    >>> fml1 = ConjFml()
    >>> fml1.add([x==1,y==2, Or(x>=0, y<=1)], update=True)
    >>> fml1.unprimed
    [x, y]
    >>> fml1.primed
    [_p_x, _p_y]
    >>> fml1.unprimed[0].sort()
    Int
    >>> fml1.primed[0].sort()
    Int
    >>> fml.update_vars()
    >>> fml.primed
    [_p_x, _p_y]
    >>> fml.safe_varlist
    True

    """
    #First, dump all vars into a list.
    self.unprimed = []
    for clause in self:
      self.unprimed.extend(get_vars(clause))
    #Now, remove dupes while preserving order.
    self.unprimed = list(dict.fromkeys(self.unprimed))
    # Add "_p_" to var names to denote primed vars and create new Ints
    self.primed = Ints(map(lambda s: "_p_"+s, list(map(str,self.unprimed))))
    
    self.safe_varlist = True 

  def add(self, *args, update=False):
    """
    Similar to Goal.add() method, adds args to self. 
    args must be iterables over fmls.
    e.g. g.add([x==2],[y==1]), g.add(g) are valid calls, but g.add(x==2), g.add(x==2,y==1) are not.
    Also updates variables and converts self to strict CNF by calling simplify.
    Only use this method to add fmls. Otherwise fmls may not be in canonical form.
    
    update is disabled by default so that list of variables is not generated on adding every clause, that would be wasteful.

    Since ConjFml is 'iterable'(read code comments for details) we can write entire query as ConjFml object.

    Need to simplify() at the end because everything needs to be in terms of <= and =, otherwise equality, 
    double negation elimination and other things will not work as expected.

    >>> g = ConjFml()
    >>> g.add([x==2],[y==1])
    >>> g
    [x == 2, y == 1]
    >>> g.add([x==2,y==1])
    >>> g
    [x == 2, y == 1, x == 2, y == 1]
    >>> g.add(x==2)
    Traceback (most recent call last):
      File "<stdin>", line 1, in <module>
      File "/home/akshay/Colg_files/SASS/formula.py", line 123, in add
        if isinstance(iter(arg), Iterable): #if arg is a goal, conjfml or list of fmls
    TypeError: 'BoolRef' object is not iterable
    >>> f = ConjFml()
    >>> f.add([x>=2, y<=3, x<3, y>4, x==y, x!=9, x == y+3])
    >>> f
    [x >= 2,
     y <= 3,
     Not(3 <= x),
     Not(y <= 4),
     x == y,
     Not(x == 9),
     x == 3 + y]
    >>> fml1 = ConjFml()
    >>> fml1.add([x==1,y==2, Or(x>=0, y<=1)], update=True)
    >>> fml1.unprimed
    [x, y]
    >>> fml1.primed
    [_p_x, _p_y]

    """
    fmls = []
    for fml in args:
      #Use iter(arg) since goal object is not Iterable. But goal works in for loop and iter(goal) does not complain about goal not being iterable. Weird shit!!
      #Explanation: iter(and also 'in' keyword) falls back to the old __getitem__  method if __iter__ is not found. So strictly speaking Goal is not an instance of Iterable, but is iterable in practice.
      if isinstance(iter(fml), Iterable): #if arg is a goal, conjfml or list of fmls
        fmls.extend(fml)
      else:
        raise TypeError
    #simplify each formula so it's in canonical form. o/w equality etc won't work as expected.
    fmls = simplifyAll(fmls)
    super(ConjFml, self).add(fmls)
    self.safe_varlist = False

    self.solver.add(fmls)

    if update:
      self.update_vars()

  def difference(self, clauses):
    """
    returns a copy of self with the given clauses removed.(Clauses given as ConjFml. Allow lists?) 
    Since Goal/ConjFml do not support deletion, use this method instead.

    >>> g = ConjFml()
    >>> g.add([x>=3, y<=4,y>x])
    >>> temp = ConjFml()
    >>> temp.add([y<=4,x==y])
    >>> g.difference(temp)
    [x >= 3, Not(y <= x)]
    """
    acc, newConj = [], ConjFml()

    for clause in self:
      if clause not in clauses:
        acc.append(clause)
    
    newConj.add(acc)
    newConj.update_vars()
    newConj.solver.add(acc)
    return newConj

  def as_primed(self):
    """
    Returns entire goal in primed form. i.e. Replaces unprimed vars with primed ones. Be careful not to call on Transition or on an already primed formula. No checks are performed to prevent this.

    Note that it returns a Goal and not a formula. Use as_expr() to obtain formula.
    """
    if not self.safe_varlist:
      self.update_vars()
    f = Goal()
    f.add([ substitute(clause, list(zip(self.unprimed, self.primed))) for clause in self  ])
    return f

  def get_primed(self, ownClause):
    """
    Return given clause of self in primed form.
    """
    # if ownClause not in self: #slow, disable, can use sets to speed this up and also allow deletion.
      # raise Exception("Clause not in ConjFml object!")
    if not self.safe_varlist:
      self.update_vars()
    return substitute(ownClause, list(zip(self.unprimed, self.primed)))

  def preimage(self, cube, trans):
    """
    Return preimage(as list of cubes) of frame(self) by doing existential quantification over primed variables in trans.
    trans, cube must be as BoolRef.

    Note: If transition is given in CNF(ConjFml/Goal), z3 hogs memory.

    Assumes that Implies is not a subformula after existential quantification. Everthing(to_NNF, to_binary, to_DNF) depends on this.

    What about incrementality in finding of preimage? Is it possible in Z3? - future wurk.
    
    These tests are obsolete.
    >>> x,y,_p_x,_p_y = Ints('x y _p_x _p_y')
    >>> T = Or(And(_p_x==x+2,x<8),And(_p_y==y-2,y>0),And(x==8,_p_x==0),And(y==0,_p_y==8))
    >>> F = ConjFml()
    >>> F.add([x>=0,y>=0,y<=20,x<=20], update=True)
    >>> cube = ConjFml()
    >>> cube.add([x==4,y==4])
    >>> F.preimage(cube,T)
    [[x == 2, y >= 0, y <= 20], [x >= 0, x <= 20, y == 6]]
       
    """

    if not isinstance(trans, BoolRef):
      raise TypeError("Invalid type for transition system. Must be BoolRef.")

    # split_all = Then(Tactic('simplify'),Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))))
    """
    On appliying a tactic to a goal, the result is a list of subgoals s.t. the original goal is satisfiable iff at least one of the subgoals is satisfiable.
    i.e. disjunction of goals. But each subgoal may not be a conjuct of constraints. Applying this tactical splits subgoals such that each subgoal is a conjunct of atomic constraints. If input is in CNF then o/p is in DNF.
    """
    propagate = Repeat(OrElse(Then(Tactic('propagate-ineqs'),Tactic('propagate-values')),Tactic('propagate-values')))  # Propagate inequalities and values.
    qe = Tactic('qe')           # Quantifier Elim.
    #TODO: Add solve-eqns tactic to do gaussian elimination after propagatoin.

    if not cube.safe_varlist:
     cube.update_vars()

    allPrimedVars = []
    allPrimedVars.extend(cube.primed)
    allPrimedVars.extend([var for var in set(get_vars(T)) if str(var)[0:3] == '_p_'])

    preimg = qe(Exists((allPrimedVars), And(self.as_expr(), trans, cube.as_primed().as_expr())))
    # preimg = qe(Exists((allPrimedVars), And(self, trans, Not(cube.as_expr()), cube.as_primed().as_expr())))
    
    #Convert preimg to DNF without converting to CNF first.
    preimg_dnf = []
    for subgoal in preimg:
      preimg_dnf.extend(to_DNF(subgoal.as_expr()))
    
    preimg_cubes = []
    for cube in preimg_dnf:
      preimg_cubes.extend(propagate(cube))

    #----- Check preimg <=> preimg_cubes -----
    # s = Solver()
    #----------------------------------------

    return preimg_cubes

def powerset(iterable):
    """
    Recipe from itertools doc page.
    powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)
    """
    s = list(iterable)
    return itertools.chain.from_iterable(itertools.combinations(s, r) for r in range(1,len(s)+1))

def generalize_unsat(init, frame, trans, cube):
  """
  Takes the cube(as ConjFml) to be generalized and returns generalized cube.
  Untested.
  """
  s, t = Solver(), Solver()
  s.add(frame,trans)

  for subset in powerset(cube): #Find smallest subset of constraints from cube that keep the query unsat.
    gcube = ConjFml()
    # print("Trying to gen: ", And(subset))
    gcube.add([And(subset)]) if len(subset) > 1 else gcube.add(subset)
    # print(gcube)
    s.push()
    # s.add(Not(cube.as_expr()), gcube.as_primed())
    s.add(Not(gcube.as_expr()), gcube.as_primed())

    t.reset() #clean up prev.
    t.add(init, gcube)

    if s.check() == unsat and t.check() == unsat:
      break

    s.pop()

  if t.check() == sat:
    exit("P not satisfied.")

  gcube = simplifyAll(gcube)

  genCube = ConjFml()
  genCube.add(gcube)
  
  return genCube

def generalize_unsat_opt(init, frame, trans, cube):
  """
  Faster version of generalization. Decision tree/binary search like approach.

  Takes advantage of the fact that, if a set of constraints is satisfiable then no subset of it is UNSAT.
  """
  s, t = Solver(), Solver()
  s.add(frame,trans)

  n = len(cube)


def to_ConjFml(fml):
  """
  Takes a BoolRef and returns equivalent in CNF as ConjFml.

  Intended for use only on Not(cube), Not(clause). Thus guranteed not to introduce extra tseitin variables.

  >>> to_ConjFml(x<8)
  [Not(8 <= x)]
  >>> to_ConjFml(Not(x>=8))
  [Not(x >= 8)]

  """
  if not isinstance(fml, z3.z3.BoolRef):
    raise TypeError("%s is not of type BoolRef." % fml)
  else:
    cnj = ConjFml()
    tsi = Tactic('tseitin-cnf')
    cnf = tsi(fml) #cnf is list of Goals
    assert(len(cnf) == 1)
    cnj.add(cnf[0].simplify())
    return cnj

def product(fmls):
  """
  Not used.

  >>> product([[x>1,x<1]])
  [[x > 1], [x < 1]]
  >>> product([[x>1],[x<1]])
  [[x > 1, x < 1]]
  >>> product([[x>1],[x<3,x>3],[x>=2]])
  [[x > 1, x < 3, x >= 2], [x > 1, x > 3, x >= 2]]
  """
  return [list(e) for e in itertools.product(*fmls)]

def is_atomic(fml):
  """
  A fml is atomic if either is_eq, is_le, is_lt, is_ge, is_gt.
  is_arith() not required since we only deal with eqs and ineqs.

  Note: Canonical formulas only use leq, geq, eq with Not(geq) to represent le.
  True is a python boolean exp. Hence, is_true(True) -> False. But is_true(simplify(x==x)) -> True.
  """
  atomics = [is_true, is_false, is_eq, is_le, is_lt, is_ge, is_gt] # is_arith]
  for at in atomics:
    if at(fml):
      return True
  return False

def is_leaf(fml):
  """
  Return true if fml is a leaf in an NNF formula.
  """
  return is_atomic(fml) or is_not(fml)

def to_NNF(fml):
  """
  Takes an arbitrary BoolRef and returns another in canonical NNF.

  >>> to_NNF(Not(And(x>=8,y<9)))
  Or(Not(x >= 8), 9 <= y)
  >>> to_NNF(Or(And(x>=8,y<9),Not(Or(x==4,And(x==x+1,y<1)))))
  Or(And(x >= 8, Not(9 <= y)),
     And(Not(x == 4), Or(True, 1 <= y)))

  """
  if is_atomic(fml):
    return simplify(fml)
  elif is_or(fml):
    return Or([to_NNF(child) for child in fml.children()])
  elif is_and(fml):
    return And([to_NNF(child) for child in fml.children()])
  elif is_not(fml):
    assert(len(fml.children())) == 1
    child = fml.children()[0]
    if is_atomic(child):
      return simplify(Not(child))
    elif is_not(child):
      assert(len(child.children())) == 1
      return to_NNF(child.children()[0])
    elif is_and(child):
      return Or([to_NNF(Not(child)) for child in child.children()])
    elif is_or(child):
      return And([to_NNF(Not(child)) for child in child.children()])
    else:
      raise RuntimeError("Unexpected BoolRef formula encountered.")
  else:
    raise RuntimeError("Unexpected BoolRef formula encountered.")

def to_binary(fml):
    """
    Takes NNF fml and converts it to binary form, i.e. each operation(or,and) has exactly two arguments.

    >>> to_binary(And(x > 1, y < 4, x > y))
    And(And(x > 1, y < 4), x > y)
    >>> to_binary(Or(And(x >= 2, x <= 2, Not(8 <= x)),And(y >= 6, y <= 6, Not(y <= 0))))
    Or(And(And(x >= 2, x <= 2), Not(x >= 8)),
       And(And(y >= 6, y <= 6), Not(y <= 0)))

    """
    if is_leaf(fml):
      return fml
    elif is_or(fml):
      acc = to_binary(fml.children()[0])
      for child in fml.children()[1:]:
        acc = Or(acc, to_binary(child))
      return acc
    elif is_and(fml):
      acc = to_binary(fml.children()[0])
      for child in fml.children()[1:]:
        acc = And(acc, to_binary(child))
      return acc
    else:
      raise RuntimeError("Unforseen type encountered.")

def to_DNF(fml):
  """
  Takes NNF fml in binary form as BoolRef and returns list of subgoals, s.t. all constraints in each subgoal are atomic.
  
  >>> to_DNF(And(x>=3,x<8,Or(y>=x,y==x+2),Or(x>y,x==y+1)))
  [[x >= 3, Not(8 <= x), y >= x, Not(x <= y)], [x >= 3, Not(8 <= x), y >= x, x == 1 + y], [x >= 3, Not(8 <= x), y == 2 + x, Not(x <= y)], [x >= 3, Not(8 <= x), y == 2 + x, x == 1 + y]]
  >>> to_DNF(x<8)
  [[Not(8 <= x)]]

  """
  def distr(a, b):
    if is_or(a):
      return Or(distr(a.children()[0],b),distr(a.children()[1],b))
    elif is_or(b):
      return Or(distr(a,b.children()[0]),distr(a,b.children()[1]))
    else:
      return And(a,b)

  def make_DNF(fml):  
    if is_and(fml):
      return distr(make_DNF(fml.children()[0]), make_DNF(fml.children()[1]))
    elif is_or(fml):
      return Or(make_DNF(fml.children()[0]), make_DNF(fml.children()[1]))
    elif is_leaf(fml):
      return fml
    else:
      raise RuntimeError

  final = []
  def flatten(fml):
    if is_or(fml):
      assert(len(fml.children()) == 2)
      flatten(fml.children()[0])
      flatten(fml.children()[1])
    else:
      final.append(to_ConjFml(fml))


  dnfFml = make_DNF(to_binary(to_NNF(fml)))

  flatten(dnfFml)
  return final

def generalize_sat(init, disjGoal, cube):
  """
  Takes a disjunctive fml which is sat, and a cube from it and returns a generalized gcube. gcube => disjFml
  disjFml is a list of Goals/ConjFml.

  Not used in block, only in main loop.
  """
  disjFml = Or([subgoal.as_expr() for subgoal in disjGoal])
  s, t = Solver(), Solver()

  for subset in powerset(cube):
    gcube = ConjFml()
    gcube.add(And(subset)) if len(subset) > 1 else gcube.add(subset)
    # print(gcube)
    s.push()
    s.add(Not(Implies(gcube.as_expr(), disjFml))) #check that gcube => disjFml

    t.reset() #clean up prev.
    t.add(init, gcube)

    if s.check() == unsat and t.check() == unsat:
      break

    s.pop()

  assert(t.check() == unsat) #What if ungeneralized cube itself intersects Init? Is that possible?
  gcube = simplifyAll(gcube)

  genCube = ConjFml()
  genCube.add(gcube)
  
  return genCube


#---------- For interactive testing ----------
x,y = Ints('x y')
g = ConjFml()
g.add([x==1, Or(x>=0, y<=1),y<2], update=True)

f = ConjFml()
f.add([x==1,y==2])

# s = EnhanSolver()
# s.add_to_query([g])

x,y,_p_x,_p_y = Ints('x y _p_x _p_y')
T = Or(And(_p_x==x+2,x<8),And(_p_y==y-2,y>0),And(x==8,_p_x==0),And(y==0,_p_y==8))
F = ConjFml()
F.add([x>=0,y>=0,y<=20,x<=20], update=True)

T = Or(And(x >= 0, x < 8, y <= 8, y > 0, _p_x == x + 2, _p_y == y - 2),And(x == 8, _p_x == 0, y == 0, _p_y == 8))
cube = ConjFml()
cube.add([x>=8])

# to_DNF(And(x>=3,Or(x<8,y>5)))
