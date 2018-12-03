 
from formula import *

from sys import exit
from heapq import heappush, heappop

do_debug = True

x,y,_p_x,_p_y = Ints('x y _p_x _p_y')
I_orig = And(x==0,y==8)
# T_orig = Or(And(x >= 0, x < 8, y <= 8, y > 0, _p_x == x + 2, _p_y == y - 2),And(x == 8, _p_x == 0, y == 0, _p_y == 8))
T_orig = Or(And(x < 8, y <= 8, _p_x == x + 2, _p_y == y - 2),And(x == 8, _p_x == 0, y == 0, _p_y == 8))
P_orig = x<8 #x<y

I = I_orig
T = T_orig #T is typically in DNF?
P = to_ConjFml(P_orig)

F1 = to_ConjFml(P_orig)
# F1 = ConjFml()
#Trace
frames = [to_ConjFml(I), F1]
#Proof obligation queue
pQueue = []

def propagate(n):
  """
  Propagates up to frontier(n).
  """
  if len(frames) <= n+1:
    frames.append(ConjFml())

  print("\nCalled propagate(%i).\n Frontier frame[%i] is: %s" % (n, n+1, frames[n+1])) if do_debug else print(end='')
  print("Frames: %s" % frames) if do_debug else print(end='')

  for k in range(1,n):
    solver = Solver()
    solver.add(T, frames[k])
    solver.push()

    for clause in set(frames[k]) - set(frames[k+1]):
      primed_clause = frames[k].get_primed(clause)
      
      solver.pop()
      solver.push()
      solver.add(Not(primed_clause))
      
      if solver.check() == unsat:
        frames[k+1].add(to_ConjFml(clause))
      # ---- Optional Subsumption check ---- #Not well-testd.
      t = Solver()
      removeList = []
      for weakClause in frames[k+1]:
        t.add(Implies(clause,weakClause))
        if t.check() == unsat: #weakClause is indeed weak.
          removeList.append(weakClause)
      frames[k+1] = frames[k+1].difference(removeList)
      # ---- -------------------------------
    
    frames[k+1] = to_ConjFml(frames[k+1].simplify().as_expr())

    if frames[k] == frames[k+1]:
      print("Frames: %s" % frames) if do_debug else print(end='')
      exit("P is valid in the system!")
  
  print("Done. Frontier frame[%i] is now: %s" % (n+1, frames[n+1])) if do_debug else print(end='')
  
  return

def block(cube, level):
  """
  Takes cube as ConjFml
  """
  heappush(pQueue, (level, cube))

  while pQueue:
    level, cube = heappop(pQueue)

    if level == 0:
      exit("P not satisfied!")
    
    solver = Solver()
    solver.add(frames[level],cube)
    
    if solver.check() == unsat: #cube is blocked at level.
      continue             #look at next obligation.

    solver.reset()
    solver.add(frames[level-1], to_ConjFml(Not(cube.as_expr())), T, cube.as_primed()) #Note:cube is a ConjFml.

    # yaSolver = Solver() #yet another solver.
    # yaSolver.add(frames[level-1], T, cube.as_primed())

    if solver.check() == sat:
      print("Preimage of %s in frame %s is: %s" % (cube, frames[level-1], cube.preimage(frames[level-1].as_expr(),T))) if do_debug else print(end='')
      print("pQueue: %s" % pQueue) if do_debug else print(end='')

      # preimg = cube.preimage(frames[level-1].as_expr(),T)
      # gPreCube = generalize_sat(I, preimg, preimg[0]) #pick a cube from preimg to generalize.
      for preCube in cube.preimage(frames[level-1].as_expr(),T):
        heappush(pQueue, (level-1, to_ConjFml(preCube.as_expr())))
      heappush(pQueue, (level, cube))
    else:
      genCube = generalize_unsat(I, frames[level-1], T, cube)
      
      print("%s is generalizedUNSAT to: %s" % (cube, genCube)) if do_debug else print(end='')
      
      for i in range(level,0,-1):
        blockingClause = to_NNF(Not(genCube.as_expr()))
        if blockingClause in frames[level]: #syntactic check
          break
        frames[i].add([blockingClause])
      #---- Optional: Push fwd. ----
      #-----------------------------

#------------ PDR Main ------------
n = 1
s = Solver()
s.add(I,Not(P.as_expr()))

if s.check() == sat:
  exit("P not satisfied in Init.")

while True:
  s.reset()
  s.add(frames[n],Not(P.as_expr()))

  if s.check() == unsat:
    # print("\nSolver: %s" % s) if do_debug else print(end='')
    propagate(n)
    n += 1
  else:
    #------- Getting model as Boolref is ugly business! Why isn't there a built-in way to do this!?!? -------
    # model = s.model()
    # variables = [ Int(str(func())) for func in model ]
    # values = [ model.eval(var) for var in variables]
    # # print(model)
    # state = ConjFml()
    # state.add([ var == val for var,val in zip(variables,values) ])
    #------------------------------------------------------------------------------------------------------
    bad_cubes = to_DNF(And(frames[n].as_expr(),Not(P.as_expr()))) if len(frames[n]) != 0 else to_DNF(Not(P.as_expr()))
    print("Bad cubes: %s" % bad_cubes) if do_debug else print(end='')

    # for bCube in bad_cubes:
    gCube = generalize_sat(I, bad_cubes, bad_cubes[0]) #pick a cube from bad_cubes to generalize.
    print(" %s generalized to %s" % (bad_cubes[0], gCube)) if do_debug else print(end='')
    print("\nCalling block(%s,%i)" % (gCube, n)) if do_debug else print(end='')
    block(gCube, n)
