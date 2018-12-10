 
from formula import *

from sys import exit
from heapq import heappush, heappop

do_debug = True

# -------------------- Input --------------------
# x, y, _p_x, _p_y = Ints('x y _p_x _p_y')
# I_orig = And(x==0,y==8)
# # T_orig = Or(And(x >= 0, x < 8, y <= 8, y > 0, _p_x == x + 2, _p_y == y - 2),And(x == 8, _p_x == 0, y == 0, _p_y == 8))
# T_orig = Or(And(x < 8, y <= 8, _p_x == x + 2, _p_y == y - 2),And(x == 8, _p_x == 0, y == 0, _p_y == 8))
# P_orig = Not(And(x==0,y==0)) #Is valid.

# x, l, _p_x, _p_l = Ints('x l _p_x _p_l')
# I_orig = And(x==0,l==0)
# T_orig = Or(And(l==0,Or(And(x<10,_p_x==x+1,_p_l==l),And(x>=10,_p_l==1,_p_x==x))),And(l==1,_p_x==x,_p_l==l))
# #TS with explicit limit for x, use for testing push forward.
# # P_orig = Or(And(l==1,x>10),l==0) #Use this prop to test push fwd. Is invalid.
# P_orig = Or(And(l==1,x==10),l==0) #This is valid.

# x, l, k, _p_x, _p_l, _p_k = Ints('x l k _p_x _p_l _p_k')
# I_orig = And(x==0,l==0, k>=0) #Dosn't work for I_orig = And(x==0,l==0) since k can be negative.
# T_orig = And(_p_k==k,Or(And(l==0,Or(And(x<k,_p_x==x+1,_p_l==l),And(x>=k,_p_l==1,_p_x==x))),And(l==1,_p_x==x,_p_l==l)))
# P_orig = Or(And(l==1,x>k),l==0) #This isn't valid.
# # P_orig = Or(And(l==1,x==k),l==0) #This is valid!

#simple_vardep
# i, j, k, l, _p_i, _p_j, _p_k, _p_l = Ints('i j k l _p_i _p_j _p_k _p_l')
# I_orig = And(i==0,j==0,k==0,l==0)
# T_orig = Or(And(l==0,Or(And(k<100,_p_i==i+1,_p_j==j+2,_p_k==k+3,_p_l==l),And(k>=100,_p_i==i,_p_j==j,_p_k==k,_p_l==1))), And(l==1,_p_i==i,_p_j==j,_p_k==k,_p_l==l))
# P_orig = And(k == 3*i, j == 2*i) #This is valid. 
# # P_orig = Or(l==0,k>3*i) #Use this to test push forward. Not valid.

#------------ PDR Main ------------
def pdr(I, T, P):

  comp = ConjFml()
  comp.add([z_false])

  F1 = to_ConjFml(P_orig)
  # F1 = ConjFml()
  #Trace
  frames = [to_ConjFml(I), F1]
  #Proof obligation queue
  pQueue = []
  n = 1
  
  def propagate(n):
    """
    Propagates up to frontier(n).
  
    For large global TS, keep two solvers per frame? One with TS the other without. ???

    Future wurk: Modify solver CDCL to maintain a table of implied clauses to make subsumption check go faster.
    """
    nonlocal pQueue, frames, comp

    if len(frames) <= n+1:
      frames.append(ConjFml())

    print("\nCalled propagate(%i).\n Frontier frame[%i] is: %s" % (n, n+1, frames[n+1])) if do_debug else print(end='')
    print("Frames: %s" % frames) if do_debug else print(end='')

    for k in range(1,n):
      frames[k].solver.push()
      frames[k].solver.add(T)

      for clause in set(frames[k]) - set(frames[k+1]):
        primed_clause = frames[k].get_primed(clause)
        
        if frames[k].solver.check(Not(primed_clause)) == unsat:
          frames[k+1].add(to_ConjFml(clause))
        # ---- Optional Subsumption check ---- #Not well-testd.
        t = Solver()        #Maybe modify solver CDCL to maintain a table of implied clauses to make this go faster,
        removeList = []
        for weakClause in frames[k+1]:
          if t.check(Implies(clause,weakClause)) == unsat: #weakClause is indeed weak.
            removeList.append(weakClause)
        frames[k+1] = frames[k+1].difference(removeList)
        # ---- -------------------------------
      frames[k].solver.pop() #Remove TS
      
      frames[k+1] = to_ConjFml(frames[k+1].simplify().as_expr())

      if frames[k] == frames[k+1]:
        print("Frames: %s" % frames) if do_debug else print(end='')
        exit("P is valid in the system!\n Fix-point is %s \n\n  Took %i propagations." % (frames[k],n))
    
    print("Done. Frontier frame[%i] is now: %s" % (n+1, frames[n+1])) if do_debug else print(end='')
    
    return

  def block(cube, level):
    """
    Takes cube as ConjFml
    """
    nonlocal pQueue, frames, n, comp

    heappush(pQueue, (level, cube))

    while pQueue:
      level, cube = heappop(pQueue)

      if level == 0:
        exit("P not satisfied!\n  Took %i propagations." % (n-1))
      
      solver = Solver()
      solver.add(frames[level],cube)
      
      if solver.check() == unsat: #cube is blocked at level.
        continue             #look at next obligation.

      solver.reset()
      solver.add(frames[level-1], to_ConjFml(Not(cube.as_expr())), T, cube.as_primed()) #Note:cube is a ConjFml.

      # yaSolver = Solver() #yet another solver.
      # yaSolver.add(frames[level-1], T, cube.as_primed())

      if solver.check() == sat:
        preimg = frames[level-1].preimage(cube,T)
        
        print("pQueue: %s" % pQueue) if do_debug else print(end='')

        preimg = [cub for cub in preimg if cub != comp]
        if preimg == []:
          continue

        print("Preimage of %s in frame %s is: %s" % (cube, frames[level-1], preimg)) if do_debug else print(end='')

        # preimg = frames[level-1].preimage(cube,T)
        # gPreCube = generalize_sat(I, preimg, preimg[0]) #pick a cube from preimg to generalize.
        for preCube in preimg:
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

  #---------- PDR Main Loop begins here ----------

  if frames[0].solver.check(Not(P.as_expr())) == sat:
    exit("P not satisfied in Init.  \nTook %i propagations." % n-1)

  while True:

    if frames[n].solver.check(Not(P.as_expr())) == unsat:
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
      # Remove [False] from bad_cubes.
      bad_cubes = [cub for cub in bad_cubes if cub != comp]

      print("Bad cubes: %s" % bad_cubes) if do_debug else print(end='')
      if len(bad_cubes) == 0: #Yikes
        pass

      # gCube = generalize_sat(I, bad_cubes, bad_cubes[0]) #pick a cube from bad_cubes to generalize. 
      # print(" %s generalized to %s" % (bad_cubes[0], gCube)) if do_debug else print(end='')
      for bCube in bad_cubes:
      # bCube = gCube
        print("\nCalling block(%s,%i)" % (bCube, n)) if do_debug else print(end='')
        block(bCube, n)

#--------- End PDR Main -----------

I = I_orig
T = T_orig #T is typically in DNF?
P = to_ConjFml(P_orig)
pdr(I, T, P)