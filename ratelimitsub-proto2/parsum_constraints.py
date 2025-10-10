import z3

## Constants
SAT = z3.sat
UNSAT = z3.unsat
UNKNOWN = z3.unknown
PROVED = UNSAT
COUNTEREXAMPLE = SAT

"""
solve(spec)

Returns SAT, UNSAT, or UNKNOWN
"""
def solve(spec):
    solver = z3.Solver()
    solver.add(spec)
    result = solver.check()
    if result == UNSAT:
        print("no solution")
    elif result == UNKNOWN:
        print("failed to solve")
    else:
        # result == SAT
        print("solution found")
        print(solver.model())
    return result


# Quick Python hack to see if Z3 is capable of solving the kinds of constraints
# we're looking at. (Perhaps can also check out Rosette solver interface or the
# OCaml bindings for Z3.)
def div_ceil(a, b):
    if a % b != 0:
        (a / b) + 1
    else:
        a / b

# Check if (5/10 || 7/5) <: (38/30 || 2/1).
def check1():
    a1 = z3.Int('a1')
    a2 = z3.Int('a2')
    b1 = z3.Int('b1')
    b2 = z3.Int('b2')
    # TODO: We don't have any way of doing floor or ceiling yet (and this may
    # in fact be impossible). Update: we do now with the extra % modulo constraints.
    cl0 = z3.And(a1 > 0, a2 > 0, b1 > 0, b2 > 0)
    cl1 = z3.Implies(b1 <= 5, a1 == 12)
    cl2 = z3.Implies(z3.And(b1 > 5, b1 <= 10, b1 % 5 == 0), a1 == 5 + 7 * (b1 / 5))
    cl9 = z3.Implies(z3.And(b1 > 5, b1 <= 10, b1 % 5 != 0), a1 == 5 + 7 * ((b1 / 5) +1))
    cl3 = z3.Implies(z3.And(b1 > 10, b1 % 10 == 0, b1 % 5 == 0), a1 == 5 * (b1 / 10) + 7 * (b1 / 5))
    cl10 = z3.Implies(z3.And(b1 > 10, b1 % 10 != 0, b1 % 5 == 0), a1 == 5 * ((b1 / 10) + 1) + 7 * (b1 / 5))
    cl11 = z3.Implies(z3.And(b1 > 10, b1 % 10 == 0, b1 % 5 != 0), a1 == 5 * (b1 / 10) + 7 * ((b1 / 5) + 1))
    cl12 = z3.Implies(z3.And(b1 > 10, b1 % 10 != 0, b1 % 5 != 0), a1 == 5 * ((b1 / 10) + 1) + 7 * ((b1 / 5) + 1))
    cl4 = z3.Implies(z3.And(b2 <= 1, 1 % b2 == 0, 30 % b2 == 0), a2 == (2 / (1 / b2) + (38 / (30 / b2))))
    cl13 = z3.Implies(z3.And(b2 <= 1, 1 % b2 != 0, 30 % b2 == 0), a2 == (2 / (1 / b2 + 1) + (38 / (30 / b2))))
    cl14 = z3.Implies(z3.And(b2 <= 1, 1 % b2 == 0, 30 % b2 != 0), a2 == (2 / (1 / b2) + (38 / (30 / b2 + 1))))
    cl15 = z3.Implies(z3.And(b2 <= 1, 1 % b2 != 0, 30 % b2 != 0), a2 == (2 / (1 / b2 + 1) + (38 / (30 / b2 + 1))))
    cl5 = z3.Implies(z3.And(b2 > 1, b2 <= 30, 30 % b2 == 0), a2 == 2 + (38 / (30 / b2)))
    cl16 = z3.Implies(z3.And(b2 > 1, b2 <= 30, 30 % b2 != 0), a2 == 2 + (38 / (30 / b2 + 1)))
    cl6 = z3.Implies(b2 > 30, a2 == 40)
    cl7 = z3.Implies(z3.And(b1 <= b2, b2 % b1 == 0), a1 * (b2 / b1) <= a2)
    cl17 = z3.Implies(z3.And(b1 <= b2, b2 % b1 != 0), a1 * (b2 / b1 + 1) <= a2)
    cl8 = z3.Implies(b1 > b2, a1 <= a2)
    solve(z3.And(cl0,cl1,cl2,cl3,cl4,cl5,cl6,cl7,cl8,cl9,cl10,cl11,cl12,cl13,cl14,cl15,cl16,cl17))

check1()

# Check if (10/3 || 12/5) <: (40/4 || 10/5).
def check3():
    a1 = z3.Int('a1')
    a2 = z3.Int('a2')
    b1 = z3.Int('b1')
    b2 = z3.Int('b2')
    cl0 = z3.And(a1 > 0, a2 > 0, b1 > 0, b2 > 0)
    cl1 = z3.Implies(b1 <= 3, a1 == 22)
    cl2 = z3.Implies(z3.And(b1 > 3, b1 <= 5, b1 % 3 == 0), a1 == 10 * (b1 / 3) + 12)
    cl9 = z3.Implies(z3.And(b1 > 3, b1 <= 5, b1 % 3 != 0), a1 == 10 * ((b1 / 3) + 1) + 12)
    cl3 = z3.Implies(z3.And(b1 > 5, b1 % 3 == 0, b1 % 5 == 0), a1 == 10 * (b1 / 3) + 12 * (b1 / 5))
    cl10 = z3.Implies(z3.And(b1 > 5, b1 % 3 != 0, b1 % 5 == 0), a1 == 10 * ((b1 / 3) + 1) + 12 * (b1 / 5))
    cl11 = z3.Implies(z3.And(b1 > 5, b1 % 3 == 0, b1 % 5 != 0), a1 == 10 * (b1 / 3) + 12 * ((b1 / 5) + 1))
    cl12 = z3.Implies(z3.And(b1 > 5, b1 % 3 != 0, b1 % 5 != 0), a1 == 10 * ((b1 / 3) + 1) + 12 * ((b1 / 5) + 1))
    cl4 = z3.Implies(z3.And(b2 <= 4, 4 % b2 == 0, 5 % b2 == 0), a2 == (40 / (4 / b2) + (10 / (5 / b2))))
    cl13 = z3.Implies(z3.And(b2 <= 4, 4 % b2 != 0, 5 % b2 == 0), a2 == (40 / (4 / b2 + 1) + (10 / (5 / b2))))
    cl14 = z3.Implies(z3.And(b2 <= 4, 4 % b2 == 0, 5 % b2 != 0), a2 == (40 / (4 / b2) + (10 / (5 / b2 + 1))))
    cl15 = z3.Implies(z3.And(b2 <= 4, 4 % b2 != 0, 5 % b2 != 0), a2 == (40 / (4 / b2 + 1) + (10 / (5 / b2 + 1))))
    cl5 = z3.Implies(z3.And(b2 > 4, b2 <= 5, 4 % b2 == 0), a2 == 40 + (10 / (5 / b2)))
    cl16 = z3.Implies(z3.And(b2 > 4, b2 <= 5, 4 % b2 != 0), a2 == 40 + (10 / (5 / b2 + 1)))
    cl6 = z3.Implies(b2 > 5, a2 == 50)
    cl7 = z3.Implies(z3.And(b1 <= b2, b2 % b1 == 0), a1 * (b2 / b1) <= a2)
    cl17 = z3.Implies(z3.And(b1 <= b2, b2 % b1 != 0), a1 * (b2 / b1 + 1) <= a2)
    cl8 = z3.Implies(b1 > b2, a1 <= a2)
    solve(z3.And(cl0,cl1,cl2,cl3,cl4,cl5,cl6,cl7,cl8,cl9,cl10,cl11,cl12,cl13,cl14,cl15,cl16,cl17))

check3()

# Check if (5/10 || 7/5) . (60/200 || 10/80) <: (600/10000 || 1000/9000).
def check2():
    a1 = z3.Int('a1')
    a2 = z3.Int('a2')
    a3 = z3.Int('a3')
    b1 = z3.Int('b1')
    b2 = z3.Int('b2')
    b3 = z3.Int('b3')
    cl0 = z3.And(a1 > 0, a2 > 0, a3 > 0, b1 > 0, b2 > 0, b3 > 0)
