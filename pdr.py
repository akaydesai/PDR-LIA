 
from formula import *

from sys import exit
from heapq import heappush, heappop

I = 
T = 
P = 

#T is typically in DNF?
P = toConjFml(P)

#Trace
frames = [I, P]
#Proof obligation queue
pQueue = []

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

def block(cube, level):
  heappush(pQueue, (level, cube))

  while pQueue:
    level, cube = heappop(pQueue)

    if level == 0:
      exit("P not satisfied!")
    
    t = Solver()
    t.add(frames[k],cube)
    if t.check() == unsat: #cube is blocked at level.
      continue             #look at next obligation.

    s = EnhanSolver()
    s.add_to_query([frames[k-1], toConjFml(Not(cube)), T, cube.as_primed()]) #Note:cube is a ConjFml.
    if s.is_sat():
      
    else:
      genCube = s.generalize_unsat(I, cube)
      for i in range(k,0,-1):
        nc = to_ConjFml(Not(cube))[0]
        if nc in frames[k]: #syntactic check
          break
        frames[i].add([nc])
      #---- Optional: Push fwd. ----
      #-----------------------------