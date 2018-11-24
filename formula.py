"""
Module containing all the data structures for handling formulas.

Prereqs: pip3 install z3-solver bidict
"""

from z3 import *  #..bad!
from z3.z3util import get_vars

from collections import Iterable
from bidict import bidict

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
  def __init__(self, id):
    """
    Constructor
    >>> g = ConjFml('test_g')
    >>> g.id
    'test_g'
    >>> g = ConjFml(2)
    Traceback (most recent call last):
      File "/usr/lib/python3.6/doctest.py", line 1330, in __run
        compileflags, 1), test.globs)
      File "<doctest formula.ConjFml.__init__[3]>", line 1, in <module>
        g = ConjFml(2)
      File "/home/akshay/Colg_files/SASS/formula.py", line 40, in __init__
        raise TypeError("Non-string type id given.")
    TypeError: Non-string type id given.
    """
    if not isinstance(id, str):
      raise TypeError("Non-string type id given.")

    # self._index = -1
    self.id = id
    self.unprimed = []
    self.primed = []
    self.safe_varlist = True 
    super(ConjFml, self).__init__()

  def __eq__(self, other):
    """
    Equal iff of same type and have the same clauses. id doesn't matter.

    >>> g = ConjFml('test_g')
    >>> f = ConjFml('test_f')
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
    >>> fml = ConjFml('whatev')
    >>> fml.add([x==1,y==2, Or(x>=0, y<=1)])
    >>> fml.unprimed
    []
    >>> fml.primed
    []
    >>> fml1 = ConjFml('whatev1')
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

    >>> g = ConjFml('test')
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
    >>> f = ConjFml('test_f')
    >>> f.add([x>=2, y<=3, x<3, y>4, x==y, x!=9, x == y+3])
    >>> f
    [x >= 2,
     y <= 3,
     Not(3 <= x),
     Not(y <= 4),
     x == y,
     Not(x == 9),
     x == 3 + y]
    >>> fml1 = ConjFml('whatev1')
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

    >>> g = ConjFml('test')
    >>> g.add([x>=3, y<=4,y>x])
    >>> temp = ConjFml('temp')
    >>> temp.add([y<=4,x==y])
    >>> g.difference(temp)
    [x >= 3, Not(y <= x)]
    """
    acc, newConj = [], ConjFml(clauses.id)

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

  def preimage(self, fml, trans):
    """
    Return preimage(as ConjFml) of self(wrt given formula(as ConjFml) -e.g. fml:=toConjFml(And(frames[k-1], !cube))) by doing existential quantification over primed variables.

    #If transition is given in CNF, z3 hogs memory.
    
    >>> x,y,_p_x,_p_y = Ints('x y _p_x _p_y')
    >>> T = Or(And(_p_x==x+2,x<8),And(_p_y==y-2,y>0),And(x==8,_p_x==0),And(y==0,_p_y==8))
    >>> F = ConjFml('test')
    >>> F.add([x==4,y==4], update=True)
    
    """
    split_all = Repeat(OrElse(Tactic('split-clause'), Tactic('skip')))
    """
    On appliying a tactic to a goal, the result is a list of subgoals s.t. the original goal is satisfiable iff at least one of the subgoals is satisfiable.
    i.e. disjunction of goals. But each subgoal may not be a conjuct of constraints. Applying this tactical splits subgoals such that each subgoal is a conjunct of atomic constraints.
    """
    qe = Tactic('qe')

    if not self.safe_varlist:
      self.update_vars()

    preimg = qe(Exists((self.primed), And(fml.as_expr(), trans , self.as_primed().as_expr())))
    preimg_cubes = []
    for subgoal in preimg:
      for fml in split_all(subgoal):
        preimg_cubes.append(fml.simplify()) #simplify to put in canonical form.
    
    return preimg_cubes

class EnhanSolver(Solver):
  """
  Extended solver class with methods to abstract away adding labels to formulas(for unsat core).

  And maybe other things.
  #Implement two way hashtable/dictionary mapping labels to clauses
  """

  def __init__(self):
    self.table = bidict()  #fml <-> uniq label.
    self.safe_solver = True
    super(EnhanSolver, self).__init__()

  def reset(self):
    """
    reset also needs to clean up clauseLabels and table.
    """
    self.table = bidict()
    self.safe_solver = True #solver contents same as table.
    super(EnhanSolver, self).reset()


  def add_to_query(self, conjfmls):
    """
    Given a list of ConjFmls, check if their conjunction is sat. i.e. Adds conjunction of ConjFmls to solver(self).
    Also labels each clause, so that unsat_core can be generated and analyzed. Returns True if sat, False otherwise.
    
    If you want unsat core, then use ONLY this method to add queries.

    PROBELMS/QUESTIONS/TODO
    1. Does removing s with pop(), preserve unsat core? i.e. Does unsat_core still contain clauses from s?
    Yes. It's preserved.

    IMPORTANT: Make sure that the cube to be generalized is the last formula added to the query. Otherwise its labels might get overwritten.
    """
    # self.push() #Do not do this. Let the user explicitly push() wherever required

    #Add labels for each clause.
    for conjfml in conjfmls:
      for i, clause in zip(range(0,len(conjfml)), conjfml):
        #Check that children of clause are atomic. Not(x<=y) is atomic.
        #That'd be slow, skip.
        label = str((conjfml.id,i))
        #Add each clause to dict with itself as key, and label as value.
        #So that the label is updated with the latest formula the clause appears in. 
        self.table.forceput(label, clause)

    self.safe_solver = False
    
  def is_sat(self):
    """
    Similar to check() method but with labels.
    """
    if not self.safe_solver:
      for label in self.table.keys():
        self.assert_and_track(self.table[label], label)
      self.safe_solver = True 

    # return self.check(Bools(self.table.keys())) == sat  #Don't need to add labels in check() if constraints were added using assert_and_track
    return self.check() == sat

  def generalize_unsat(solver, init, trans, cube): #Bad design.
    """
    Takes the cube to be generalized and init states(as ConjFml) and returns generalized cube.
    Note that F,T,and cube are all in solver at this point.

    Generalization is done by returning only those clauses from cube which occur in the unsat core. But if this intersects init, then we block Not(init).
    TODO: Test the ungeneralization.
    """
    #Expanded for clarity: [ cube.get(int(str(label).split()[1])) for label in solver.unsat_core() if cube.id == str(str(label).split()[0])]
    
    acc = []
    g = ConjFml("gencube")
    
    for label in solver.unsat_core():
      lbl_id, lbl_clauseNum = eval(str(label))
      if cube.id == lbl_id:
        acc.append(cube.get(lbl_clauseNum))

    acc = simplifyAll(acc)
    #Check if query still unsat? Nah.. not need.
    #But we need to make sure acc does not intersect initial states.
    #TODO: Test this.
    s = Solver()
    #Need to get clauses correrp to label.
    s.add(init, acc)
    if s.check() == sat:
      g.add(c, toConjFml(Not(init)))
    else:
      g.add(acc)
    return g

def to_ConjFml(fml):
  """
  Takes a BoolRef and returns equivalent in CNF as ConjFml.

  Intended for use only on Not(cube), Not(clause). Thus guranteed not to introduce extra tseitin variables.
  """
  if not isinstance(fml, z3.z3.BoolRef):
    raise TypeError
  else:
    tsi = Tactic('tseitin-cnf')
    cnf = tsi(fml) #cnf is list of Goals
    assert(len(cnf) == 1)
    return cnf[0]

#---------- For interactive testing ----------
x,y = Ints('x y')
g = ConjFml('test_g')
g.add([x==1, Or(x>=0, y<=1),y<2], update=True)

f = ConjFml('test_f')
f.add([x==1,y==2])

s = EnhanSolver()
s.add_to_query([g])