 
from formula import *

from sys import exit

I = 
T = 
P = 

# T = toConjFml(T) #T is typically in DNF?
P = toConjFml(P)

frames = [I, P]

def propagate(n):
  """
  """
  frames[n+1] = True
  
  for k in range(1,n):
    s = Solver()
    s.add(T, frames[k])

    for clause in set(frames[k]) - set(frames[k+1]):
      primed_clause = frames[k].getPrimed(clause)
      s.add(Not(primed_clause))
      if s.check() == unsat:
        frames[k+1].add([toConjFml(Not(clause))])

        #---- Optional Subsumption check ----
        t = Solver()
        t.add(clause)
        removeList = []
        for weakClause in frames[k+1]:
          t.add(Not(weakClause))
          if t.check() == unsat: #weakClause is indeed weak.
            removeList.append(weakClause)
        frames[k+1] = frames[k+1].difference(removeList)
        #---- -------------------------- ----
        if frames[k] == frames[k+1]:
          exit("P is valid in the system!")
  return

def block():

