# (set-option :produce-unsat-cores true)
# (declare-const x Int)
# (assert (exists ((x Int)) (and (> x 0) (< x 5)) ) )
# (check-sat)
# (get-model)

# (define-fun testfn ((x Int)) Bool
#  (exists ((x Int)) (and (and (> x 0) (< x 5)) (< x 0) ) )
# )

# (assert testfn)
# (check-sat)
# (get-unsat-core)

# ;no apparent suppport for quantifier elim in smtlib2 format, try z3py.

from z3 import *
x,y,xp,yp = Ints('x y xp yp')
t = Tactic('qe')
# https://stackoverflow.com/questions/20682763/z3-does-qe-tactic-preserve-equivalence-or-only-equisatisfiability
    # qe: preserves validity. It eliminates quantifiers from formulas producing equivalent formulas.
    # qe-sat: checks satisfiability of quantified formulas. It does not produce equivalent subgoals.
    # qe-lite: light-weight quantifier elimination. It preserves equivalence, but does not always eliminate quantifiers. It tries to eliminate quantifiers that are cheap to reduce.


t(Exists((xp, yp), And(xp==x+1, yp==y+2, xp<=8, xp >=1, yp<=12, yp>=2)))
# Almost certain this is the same as t.apply(formula)
# [[y <= 10, y >= 0, x <= 7, x >= 0]] #interpreted as conjunction. tsietin-cnf leaves this unchanged.

T = Implies(x<10 , And(xp==x+1, yp==y+2, xp<=8, xp >=1, yp<=12, yp>=2))
preimg = t(Exists((xp, yp), T)) #preimage
print(preimg)
# [[Or(10 <= x, And(y <= 10, y >= 0, And(x <= 7, x >= 0)))]]

# From: https://www.cs.tau.ac.il/~msagiv/courses/asv/z3py/strategies-examples.htm
split_all = Repeat(OrElse(Tactic('split-clause'), Tactic('skip')))
#Need to convert output to DNF as list of subgoals using tacticals.
result = []
for subgoal in preimg:
  for fml in split_all(subgoal):
    result.append(fml.simplify()) #simplify may not be required.

#Convert to CNF using tseitin-cnf tactic.
preimg = t(Exists((xp, yp), Implies(x<10 , And(xp==x+1, yp==y+2, xp<=8, xp >=1, yp<=12, yp>=2))))
tsi = Tactic('tseitin-cnf')
tsi(preimg[0])

# Checking if preimage is empty by creating solver from tactic.
s = Then('qe', 'smt').solver()
s.check(preimage[0])
# sat #means preimage is not empty. Need to generalize?

#Better to use a solver s and check disjunction of returned subgoals.

#Alternate, use Goal
#https://stackoverflow.com/questions/17911892/how-to-perform-quantifier-elimination-using-python-api-of-z3
  # x, t1, t2 = Reals('x t1 t2')
  # g = Goal()
  # g.add(Exists(x, And(t1 < x, x < t2)))
  # t = Tactic('qe')
  # print t(g)
  # [[¬(0 ≤ t1 + -1·t2)]]

#--------------------------------------------------------------------------------
# Stuff for generalisation, SMT UNSAT Core or conflict clause.

s=Solver()
x,y,z = Ints('x y z')
a,b,c, d = Bools('a b c d')

s.add(Implies(a, x <3))
s.add(Implies(b, y <3))
s.add(Implies(c, z==x+y))
s.check(a,b,c)
# sat
s.model()
# [z = 0, b = True, a = True, c = True, x = 0, y = 0]
s.add(Implies(d, z>x+y))
print(s)
# [Implies(a, x < 3),
#  Implies(b, y < 3),
#  Implies(c, z == x + y),
#  Implies(d, z > x + y)]
s.check(a,b,c,d)
# unsat
s.unsat_core()
# [d, c]

#Alternatively, use: s.assert_and_track(constraint, label); s.check();
# https://stackoverflow.com/questions/45225375/is-there-a-way-to-use-solver-unsat-core-without-using-solver-assert-and-track
# But this is the same as using Implies.
x = Int('x')
a = Bool('a')
s = Solver()
s.assert_and_track(x==1, a) #Can't pass lists of assertions and labels. :/
print(s)
# [Implies(a, x == 1)]
s.check() #No need to pass labels, unlike directly using Implies.

#Label formulas using assert_and_track(fml, fml.sexpr()) #sexpr could be very large. Create new name for each formulas

#List available tactics.
tactics()
# ['ackermannize_bv', 'subpaving', 'horn', 'horn-simplify', 'nlsat', 'qfnra-nlsat', 'nlqsat', 'qe-light', 'qe-sat', 'qe', 'qsat', 'qe2', 'qe_rec', 'vsubst', 'sat', 'sat-preprocess', 'ctx-solver-simplify', 'smt', 'unit-subsume-simplify', 'aig', 'add-bounds', 'card2bv', 'degree-shift', 'diff-neq', 'elim01', 'eq2bv', 'factor', 'fix-dl-var', 'fm', 'lia2card', 'lia2pb', 'nla2bv', 'normalize-bounds', 'pb2bv', 'propagate-ineqs', 'purify-arith', 'recover-01', 'bit-blast', 'bv1-blast', 'bv_bound_chk', 'propagate-bv-bounds', 'reduce-bv-size', 'bvarray2uf', 'dt2bv', 'elim-small-bv', 'max-bv-sharing', 'blast-term-ite', 'cofactor-term-ite', 'collect-statistics', 'ctx-simplify', 'der', 'distribute-forall', 'elim-term-ite', 'elim-uncnstr', 'snf', 'nnf', 'occf', 'pb-preprocess', 'propagate-values', 'reduce-args', 'simplify', 'elim-and', 'solve-eqs', 'split-clause', 'symmetry-reduce', 'tseitin-cnf', 'tseitin-cnf-core', 'fpa2bv', 'qffp', 'qffpbv', 'nl-purify', 'default', 'sine-filter', 'qfbv-sls', 'nra', 'qfaufbv', 'qfauflia', 'qfbv', 'qfidl', 'qflia', 'qflra', 'qfnia', 'qfnra', 'qfuf', 'qfufbv', 'qfufbv_ackr', 'qfufnra', 'ufnia', 'uflra', 'auflia', 'auflira', 'aufnira', 'lra', 'lia', 'lira', 'skip', 'fail', 'fail-if-undecided', 'macro-finder', 'quasi-macros', 'ufbv-rewriter', 'bv', 'ufbv']

#Checking implied clauses:
solver = Solver()
g = Goal()
g.add([x==1, Or(x>=0, y<=1),y<2,y<10])
[ solver.check(Not(Implies(i,j))) == unsat for j in g for i in g if not i.eq(j) ]
