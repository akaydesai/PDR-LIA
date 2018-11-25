"""
Module containing all the data structures for handling formulas.

Prereqs: pip3 install z3-solver #bidict

Doctest: python3 -m doctest formula.py [-v]
"""

from z3 import *  #..bad!
from z3.z3util import get_vars

from collections import Iterable
from functools import reduce
import itertools
# from bidict import bidict

simplifyAll = lambda l: list(map(simplify, l))
"""
Convert an Iterable of formulas into canonical form.
"""

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

  #TODO: Store clauses in a set, this would allow deletion, musch faster __contains__, but not sure if it'd be true speed up as z3 GoalObj isn't mutable.
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
    if not isinstance(other, type(self)):
      raise TypeError("'%s' is not of type '%s'." % (other,type(self)))

    if len(self) != len(other):
      return False
    else:
      return set(self) == set(other)

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

    if update:
      self.update_vars()
      self.safe_varlist = True

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

  def preimage(self, frame, trans):
    """
    Return preimage(as list of cubes) of cube(self)by doing existential quantification over primed variables.
    trans must be a BoolRef.

    If transition is given in CNF(ConjFml/Goal), z3 hogs memory. 
    
    >>> x,y,_p_x,_p_y = Ints('x y _p_x _p_y')
    >>> T = Or(And(_p_x==x+2,x<8),And(_p_y==y-2,y>0),And(x==8,_p_x==0),And(y==0,_p_y==8))
    >>> F = ConjFml()
    >>> F.add([x>=0,y>=0,y<=20,x<=20], update=True)
    >>> cube = ConjFml()
    >>> cube.add([x==4,y==4])
    >>> cube.preimage(F,T)
    [[x == 2, y >= 0, y <= 20], [x >= 0, x <= 20, y == 6]]
    
    """
    if not isinstance(trans, BoolRef):
      raise TypeError("Invalid type for transition system. Must be BoolRef.")

    split_all = Then(Tactic('simplify'),Repeat(OrElse(Tactic('split-clause'), Tactic('skip'))))
    """
    On appliying a tactic to a goal, the result is a list of subgoals s.t. the original goal is satisfiable iff at least one of the subgoals is satisfiable.
    i.e. disjunction of goals. But each subgoal may not be a conjuct of constraints. Applying this tactical splits subgoals such that each subgoal is a conjunct of atomic constraints.
    """
    propagate = Repeat(OrElse(Then(Tactic('propagate-ineqs'),Tactic('propagate-values')),Tactic('propagate-values')))  # Propagate inequalities and values.
    qe = Tactic('qe')           # Quantifier Elim.
    tsi = Tactic('tseitin-cnf') # Tseitin encoding
    #Add solve-eqns tactic for gaussian elimination.

    if not self.safe_varlist:
      self.update_vars()

    # compose = Then(Then(Then(Tactic('qe'), Tactic('tseitin-cnf')), split_all), propagate)
    # preimg_cubes = compose(Exists((self.primed), And(frame.as_expr(), trans, Not(self.as_expr()), self.as_primed().as_expr())))

    preimg = qe(Exists((self.primed), And(frame.as_expr(), trans, Not(self.as_expr()), self.as_primed().as_expr())))
    
    #Convert preimg to DNF without converting to CNF first.

    preimg_cubes = []
    for subgoal in preimg_dnf:
      # for subgoal in propagate(subgoal):
      preimg_cubes.append(subgoal.simplify()) #simplify to put in canonical form.
    
    return preimg_cubes

def powerset(iterable):
    """
    Recipe from itertools doc page.
    powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)
    """
    s = list(iterable)
    return itertools.chain.from_iterable(itertools.combinations(s, r) for r in range(1,len(s)+1))

def generalize_unsat(solver, init, frame, trans, cube): #Bad design.
  """
  Takes the cube(as ConjFml) to be generalized and returns generalized cube.

  Generalization is done by returning only those clauses from cube which occur in the unsat core. But if this intersects init, then we block Not(init).
  TODO: Test the ungeneralization.

  
  """
  s = Solver()
  s.add(frame,trans)

  for subset in powerset(cube): #Find smallest subset of constraints from cube that keep the query unsat.
    s.push()
    gcube = Goal()
    gcube.add(And(subset)) if len(subset) > 1 else gcube.add(subset)

    s.add(Not(gcube), toConjFml(cube).as_primed())

    if s.check() == unsat:
      break

    s.pop()

  gcube = simplifyAll(gcube)

  #Check if query still unsat? Nah.. not need.
  #But we need to make sure acc does not intersect initial states.
  #TODO: Test this.
  s = Solver()
  #Need to get clauses correrp to label.
  s.add(init, gcube)
  if s.check() == sat:
    gcube.add(toConjFml(Not(init)))
  
  return gcube

def to_ConjFml(fml, id=''):
  """
  Takes a BoolRef and returns equivalent in CNF as ConjFml.

  Intended for use only on Not(cube), Not(clause). Thus guranteed not to introduce extra tseitin variables.
  """
  if not isinstance(fml, z3.z3.BoolRef):
    raise TypeError
  else:
    cnj = ConjFml(id)
    tsi = Tactic('tseitin-cnf')
    cnf = tsi(fml) #cnf is list of Goals
    assert(len(cnf) == 1)
    cnj.add(cnf[0].simplify())
    return cnj

def product(fmls):
  """
  >>> product([[x>1,x<1]])
  [[x > 1], [x < 1]]
  >>> product([[x>1],[x<1]])
  [[x > 1, x < 1]]
  >>> product([[x>1],[x<3,x>3],[x>=2]])
  [[x > 1, x < 3, x >= 2], [x > 1, x > 3, x >= 2]]
  """

  return [list(e) for e in itertools.product(*fmls)]

def to_DNF(fml):
  """
  Takes NNF fml as BoolRef and returns list of goals, s.t. all constraints in each goal are atomic.
  
  We only need to split Or() fmls.
  """
  def is_atomic(fml):
    """
    A fml is atomic if either is_arith(fml) or is_eq, is_le, is_lt, is_ge, is_gt, is_not. 
    """
    atomics = [is_arith, is_eq, is_le, is_lt, is_ge, is_gt, is_not]
    return reduce(lambda a, b: a or b, [at(fml) for at in atomics])

  acc = []

  if is_atomic(fml):
    return [fml]
  elif is_or(fml):
    for child in fml.children():
      acc.extend(to_DNF(child))
    return product([acc])
  elif is_and(fml):
    for child in fml.children():
      acc.append(to_DNF(child))
    return product(acc)
  else:
    raise RuntimeError

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
cube = ConjFml()
cube.add([x==4,y==4])

# to_DNF(And(x>=3,Or(x<8,y>5)))