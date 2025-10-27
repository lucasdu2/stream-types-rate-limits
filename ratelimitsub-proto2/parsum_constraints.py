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
# NOTE: I'm not actually using this; in fact, I don't even know if it would work
# this way.
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
    # Symbolic constraints for (5/10 || 7/5), b1 is window size, a1 is resulting event count
    cl1 = z3.Implies(b1 <= 5, a1 == 12)
    cl2 = z3.Implies(z3.And(b1 > 5, b1 <= 10, b1 % 5 == 0), a1 == 5 + 7 * (b1 / 5))
    cl9 = z3.Implies(z3.And(b1 > 5, b1 <= 10, b1 % 5 != 0), a1 == 5 + 7 * ((b1 / 5) +1))
    cl3 = z3.Implies(z3.And(b1 > 10, b1 % 10 == 0, b1 % 5 == 0), a1 == 5 * (b1 / 10) + 7 * (b1 / 5))
    cl10 = z3.Implies(z3.And(b1 > 10, b1 % 10 != 0, b1 % 5 == 0), a1 == 5 * ((b1 / 10) + 1) + 7 * (b1 / 5))
    cl11 = z3.Implies(z3.And(b1 > 10, b1 % 10 == 0, b1 % 5 != 0), a1 == 5 * (b1 / 10) + 7 * ((b1 / 5) + 1))
    cl12 = z3.Implies(z3.And(b1 > 10, b1 % 10 != 0, b1 % 5 != 0), a1 == 5 * ((b1 / 10) + 1) + 7 * ((b1 / 5) + 1))
    # Symbolic constraints for (38/30 || 2/1), b2 is window size, a2 is resulting event count
    cl4 = z3.Implies(z3.And(b2 <= 1, 1 % b2 == 0, 30 % b2 == 0), a2 == (2 / (1 / b2) + (38 / (30 / b2))))
    cl13 = z3.Implies(z3.And(b2 <= 1, 1 % b2 != 0, 30 % b2 == 0), a2 == (2 / (1 / b2 + 1) + (38 / (30 / b2))))
    cl14 = z3.Implies(z3.And(b2 <= 1, 1 % b2 == 0, 30 % b2 != 0), a2 == (2 / (1 / b2) + (38 / (30 / b2 + 1))))
    cl15 = z3.Implies(z3.And(b2 <= 1, 1 % b2 != 0, 30 % b2 != 0), a2 == (2 / (1 / b2 + 1) + (38 / (30 / b2 + 1))))
    cl5 = z3.Implies(z3.And(b2 > 1, b2 <= 30, 30 % b2 == 0), a2 == 2 + (38 / (30 / b2)))
    cl16 = z3.Implies(z3.And(b2 > 1, b2 <= 30, 30 % b2 != 0), a2 == 2 + (38 / (30 / b2 + 1)))
    cl6 = z3.Implies(b2 > 30, a2 == 40)
    # Subtyping constraints
    cl7 = z3.Implies(z3.And(b1 <= b2, b2 % b1 == 0), a1 * (b2 / b1) <= a2)
    cl17 = z3.Implies(z3.And(b1 <= b2, b2 % b1 != 0), a1 * (b2 / b1 + 1) <= a2)
    cl8 = z3.Implies(b1 > b2, a1 <= a2)
    solve(z3.And(cl0,cl1,cl2,cl3,cl4,cl5,cl6,cl7,cl8,cl9,cl10,cl11,cl12,cl13,cl14,cl15,cl16,cl17))

# check1()

# Check if (5/10 || 7/5) . (60/200 || 10/80 || 42/30) <: (600/10000 || 1000/9000).
def check2():
    a1 = z3.Int('a1')
    a2 = z3.Int('a2')
    a3 = z3.Int('a3')
    b1 = z3.Int('b1')
    b2 = z3.Int('b2')
    b3 = z3.Int('b3')
    cl0 = z3.And(a1 > 0, a2 > 0, a3 > 0, b1 > 0, b2 > 0, b3 > 0)
    # Test performance if we set additional window size constraints
    # NOTE: This is much better (if our conjecture is true), and may possibly
    # even mean we can just hand-code the decision procedure instead of calling
    # out to a dedicated constraint solver! 0.2 seconds vs 3.3 seconds.
    extra1 = z3.And(b1 == b2, b2 == b3, b1 == b3)
    extra2 = z3.Or(b1 == 10, b1 == 5, b1 == 200, b1 == 80, b1 == 30, b1 == 10000, b1 == 9000)
    # Symbolic constraints for (5/10 || 7/5), b1 is window size, a1 is resulting event count
    cl1 = z3.Implies(b1 <= 5, a1 == 12)
    cl2 = z3.Implies(z3.And(b1 > 5, b1 <= 10, b1 % 5 == 0), a1 == 5 + 7 * (b1 / 5))
    cl3 = z3.Implies(z3.And(b1 > 5, b1 <= 10, b1 % 5 != 0), a1 == 5 + 7 * ((b1 / 5) +1))
    cl4 = z3.Implies(z3.And(b1 > 10, b1 % 10 == 0, b1 % 5 == 0), a1 == 5 * (b1 / 10) + 7 * (b1 / 5))
    cl5 = z3.Implies(z3.And(b1 > 10, b1 % 10 != 0, b1 % 5 == 0), a1 == 5 * ((b1 / 10) + 1) + 7 * (b1 / 5))
    cl6 = z3.Implies(z3.And(b1 > 10, b1 % 10 == 0, b1 % 5 != 0), a1 == 5 * (b1 / 10) + 7 * ((b1 / 5) + 1))
    cl7 = z3.Implies(z3.And(b1 > 10, b1 % 10 != 0, b1 % 5 != 0), a1 == 5 * ((b1 / 10) + 1) + 7 * ((b1 / 5) + 1))
    # Symbolic constraints for (600/10000 || 1000/9000), b2 is window size, a2 is resulting event count
    cl8 = z3.Implies(b2 <= 9000,
                     z3.If(9000 % b2 == 0,
                           z3.If(10000 % b2 == 0,
                                 a2 == (1000 / (9000 / b2) + (600 / (10000 / b2))),
                                 a2 == (1000 / (9000 / b2) + (600 / (10000 / b2 + 1)))),
                           z3.If(10000 % b2 == 0,
                                 a2 == (1000 / (9000 / b2 + 1) + (600 / (10000 / b2))),
                                 a2 == (1000 / (9000 / b2 + 1) + (600 / (10000 / b2 + 1))))))
    cl9 = z3.Implies(z3.And(b2 > 9000, b2 <= 10000),
                     z3.If(10000 % b2 == 0,
                           a2 == 1000 + (600 / (10000 / b2)),
                           a2 == 1000 + (600 / (10000 / b2 + 1))))
    cl10 = z3.Implies(b2 > 10000, a2 == 1600)
    # Symbolic constraints (60/200 || 10/80 || 42/30), b3..., a3...
    cl11 = z3.Implies(b3 <= 30, a3 == 60 + 10 + 42)
    cl12 = z3.Implies(z3.And(b3 > 30, b3 <= 80),
                      z3.If(b3 % 30 != 0,
                            a3 == 42 * (b3 / 30 + 1) + 10 + 60,
                            a3 == 42 * (b3 / 30) + 10 + 60))
    cl13 = z3.Implies(z3.And(b3 > 80, b3 <= 200),
                      z3.If(b3 % 80 != 0,
                            z3.If(b3 % 30 != 0,
                                  a3 == 42 * (b3 / 30 + 1) + 10 * (b3 / 80 + 1) + 60,
                                  a3 == 42 * (b3 / 30) + 10 * (b3 / 80 + 1) + 60),
                            z3.If(b3 % 30 != 0,
                                  a3 == 42 * (b3 / 30 + 1) + 10 * (b3 / 80) + 60,
                                  a3 == 42 * (b3 / 30) + 10 * (b3 / 80) + 60)))
    cl14 = z3.Implies(b3 > 200,
                      z3.If(b3 % 200 != 0,
                            z3.If(b3 % 80 != 0,
                                  z3.If(b3 % 30 != 0,
                                        a3 == 42 * (b3 / 30 + 1) + 10 * (b3 / 80 + 1) + 60 * (b3 / 200 + 1),
                                        a3 == 42 * (b3 / 30)  + 10 * (b3 / 80 + 1) + 60 * (b3 / 200 + 1)),
                                  z3.If(b3 % 30 != 0,
                                        a3 == 42 * (b3 / 30 + 1) + 10 * (b3 / 80) + 60 * (b3 / 200 + 1),
                                        a3 == 42 * (b3 / 30)  + 10 * (b3 / 80) + 60 * (b3 / 200 + 1))),
                            z3.If(b3 % 80 != 0,
                                  z3.If(b3 % 30 != 0,
                                        a3 == 42 * (b3 / 30 + 1) + 10 * (b3 / 80 + 1) + 60 * (b3 / 200),
                                        a3 == 42 * (b3 / 30)  + 10 * (b3 / 80 + 1) + 60 * (b3 / 200)),
                                  z3.If(b3 % 30 != 0,
                                        a3 == 42 * (b3 / 30 + 1) + 10 * (b3 / 80) + 60 * (b3 / 200),
                                        a3 == 42 * (b3 / 30)  + 10 * (b3 / 80) + 60 * (b3 / 200)))))
    # Subtyping constraints
    # Use concatenation rewriting rule, which produces a disjunction
    # i.e. (n1/t1 . n2/t2) equivalent to (n1+n2)/t1 ^ (n2/t2)
    # TODO: Is this even true? Who knows. I think so though, and it offers a
    # generalization of the rewrite rule we had before for matching window sizes.
    # TODO: OK, I don't think this is true. If anything, it would be:
    # (n1/t1 . n2/t2) <: (n1+n2)/t1 OR (n1+n2)/t2
    cl15 = z3.Implies(b1 <= b2, z3.If(b2 % b1 != 0, (a1 + a3) * (b2 / b1 + 1) <= a2, (a1 + a3) * (b2 / b1) <= a2))
    cl16 = z3.Implies(b1 > b2, a1 + a3 <= a2)
    cl17 = z3.Implies(b3 <= b2, z3.If(b2 % b3 != 0, a3 * (b2 / b3 + 1) <= a2, a3 * (b2 / b3) <= a2))
    cl18 = z3.Implies(b3 > b2, a3 <= a2)
    solve(z3.And(cl0,cl1,cl2,cl3,cl4,cl5,cl6,cl7,cl8,cl9,cl10,cl11,cl12,cl13,cl14,cl15,cl16,cl17,cl18,
                 extra1, extra2))

check2()


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

# check3()

# Check if (5/10 || 7/5) <: (38000500/100000 || 250940989/85823490).
def check4():
    a1 = z3.Int('a1')
    a2 = z3.Int('a2')
    b1 = z3.Int('b1')
    b2 = z3.Int('b2')

    # TODO: We don't have any way of doing floor or ceiling yet (and this may
    # in fact be impossible). Update: we do now with the extra % modulo constraints.
    cl0 = z3.And(a1 > 0, a2 > 0, b1 > 0, b2 > 0)
    # Symbolic constraints for (5/10 || 7/5), b1 is window size, a1 is resulting event count
    cl1 = z3.Implies(b1 <= 5, a1 == 12)
    cl2 = z3.Implies(z3.And(b1 > 5, b1 <= 10, b1 % 5 == 0), a1 == 5 + 7 * (b1 / 5))
    cl3 = z3.Implies(z3.And(b1 > 5, b1 <= 10, b1 % 5 != 0), a1 == 5 + 7 * ((b1 / 5) +1))
    cl4 = z3.Implies(z3.And(b1 > 10, b1 % 10 == 0, b1 % 5 == 0), a1 == 5 * (b1 / 10) + 7 * (b1 / 5))
    cl5 = z3.Implies(z3.And(b1 > 10, b1 % 10 != 0, b1 % 5 == 0), a1 == 5 * ((b1 / 10) + 1) + 7 * (b1 / 5))
    cl6 = z3.Implies(z3.And(b1 > 10, b1 % 10 == 0, b1 % 5 != 0), a1 == 5 * (b1 / 10) + 7 * ((b1 / 5) + 1))
    cl7 = z3.Implies(z3.And(b1 > 10, b1 % 10 != 0, b1 % 5 != 0), a1 == 5 * ((b1 / 10) + 1) + 7 * ((b1 / 5) + 1))
    # Symbolic constraints for (38000500/100000 || 250940989/85823490), b2 is window size, a2 is resulting event count
    cl8 = z3.Implies(z3.And(b2 <= 100000, 100000 % b2 == 0, 85823490 % b2 == 0),
                     a2 == (38000500 / (100000 / b2) + (250940989 / (85823490 / b2))))
    cl9 = z3.Implies(z3.And(b2 <= 100000, 100000 % b2 != 0, 85823490 % b2 == 0),
                      a2 == (38000500 / (100000 / b2 + 1) + (250940989 / (85823490 / b2))))
    cl10 = z3.Implies(z3.And(b2 <= 100000, 100000 % b2 == 0, 85823490 % b2 != 0),
                      a2 == (38000500 / (100000 / b2) + (250940989 / (85823490 / b2 + 1))))
    cl11 = z3.Implies(z3.And(b2 <= 100000, 100000 % b2 != 0, 85823490 % b2 != 0),
                      a2 == (38000500 / (100000 / b2 + 1) + (250940989 / (85823490 / b2 + 1))))
    cl12 = z3.Implies(z3.And(b2 > 100000, b2 <= 85823490, 85823490 % b2 == 0),
                     a2 == 38000500 + 250940989 / (85823490 / b2))
    cl13 = z3.Implies(z3.And(b2 > 100000, b2 <= 85823490, 85823490 % b2 == 0),
                     a2 == 38000500 + 250940989 / (85823490 / b2 + 1))
    cl14 = z3.Implies(b2 > 85823490, a2 == 38000500 + 250940989)
    # Subtyping constraints
    cl15 = z3.Implies(z3.And(b1 <= b2, b2 % b1 == 0), a1 * (b2 / b1) <= a2)
    cl16 = z3.Implies(z3.And(b1 <= b2, b2 % b1 != 0), a1 * (b2 / b1 + 1) <= a2)
    cl17 = z3.Implies(b1 > b2, a1 <= a2)
    solve(z3.And(cl0,cl1,cl2,cl3,cl4,cl5,cl6,cl7,cl8,cl9,cl10,cl11,cl12,cl13,cl14,cl15,cl16,cl17))

# check4()
