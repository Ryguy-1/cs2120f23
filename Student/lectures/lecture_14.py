from z3 import *

# Propositional Logic (Boolean) Variables
# Python name, variable type, string name

X = Bool("X")
Y = Bool("Y")
Z = Bool("Y")

# Propositional logic expressions
# Iff is represented by equality ==

print("And expression: ", (And(X, Y)))
print("Or expression: ", (Or(X, Y)))
print("Not expression: ", Not(X))
print("Implies expression: ", Implies(X, Y))
print("Iff expression: ", (X == Y))

# In Propositional Logic in Z3, True and False are Constant Expressions

print("True is a propositional constant: ", True)
print("False is a propositional constant: ", False)
print("Simplifying X /\ True: ", simplify(And(X, True)))
print("Simplifying X \/ False: ", simplify(Or(X, False)))

# Satisfiability Solving

print("Solving X /\ Y")
solve(And(X, Y))

print("Solving X \/ Y")
solve(Or(X, Y))

print("Solving X /\ ~X")
solve(And(X, (Not(X))))

print("Solving X \/ ~X")
solve(Or(X, Not(X)))

# Think about this one. The implication being true says what about X?
print("Solving X => False")
solve(Implies(X, False))

print("Solving (X => False) /\ X")
solve(And(Implies(X, False)), X)

print("Solve (X => Y) /\ (Y => Z)")
solve(And(Implies(X, Y), Implies(Y, Z)))

print("Solve a set of constraints")
solve(Implies(X, Y), Or(Not(X), Z), Z == Not(Y))

# There's no validity checker, but it's easy to make one
# Expression e is valid if true under every interpretation
# That's equivalent to ~e being false under every interpretation
# Z3 will tell us if an expression is "unsat"
# Just check to see if ~e is unsat; if so then e is valid

print("Unsatisfiability of negation, ~(X \/ ~X), means (X \/ ~X) is valid.")
solve(Not(Or(X, Not(X))))

# Simplification

print("Simplify X and Y and X")
print(simplify(And(X, Y, X)))

X = Int("X")
Y = Int("Y")
solve(X > 2, X < 10, Y == X + 1)


# Ryland: Video Problem 2
x, y, z = Ints("x y z")
s = Solver()
s.add(3 * x + 2 * y - z == 1)
s.add(2 * x - 2 * y + 4 * z == -2)
s.add(x + y + z == 222)

if s.check() == sat:
    print(s.model())
else:
    print("unsat")


# Ryland: Video Problem 3
s = Solver()
x = Int("x")
print(simplify(5 * (2 + x) + 3 * (5 * x + 4) - (x**2) ** 2))


# Ryland Random Problem
x, y = Ints("x y")
print(simplify(x**2 + y**2 - x**2))  # prints y**2 wow this is so cool

print(Q(1, 3))  # this is 1/3 rational number

p = Bool("p")
q = Bool("q")
r = Bool("r")
solve(Implies(p, q), r == Not(q), Or(Not(p), r))
solve(And(Implies(p, q), r == Not(q), Or(Not(p), r)))

x, y = Bools("x y")
solve(Implies(Implies(x, y), Implies(Not(x), Not(y))))

x, y, z = Reals("x y z")
s = Solver()
s.add(x > 1, y > 1, x + y > 3, z - x < 10)
print(s.check())

m = s.model()
print("x = %s" % m[x])

print("traversing model...")
for d in m.decls():
    print("%s = %s" % (d.name(), m[d]))

x = Int("x")
y = Int("y")
f = Function("f", IntSort(), IntSort())
solve(f(f(x)) == x, f(x) == y, x != y)

p, q = Bools("p q")
demorgan = And(p, q) == Not(Or(Not(p), Not(q)))
print(demorgan)


def prove(f):
    s = Solver()
    s.add(Not(f))
    if s.check() == unsat:
        print("proved")
    else:
        print("failed to prove")


print("Proving demorgan...")
prove(demorgan)

# Ima Hurryin is approaching a stoplight moving with a velocity of 30.0 m/s. The light turns yellow, and Ima applies the brakes and skids to a stop. If Ima's acceleration is -8.00 m/s2, then determine the displacement of the car during the skidding process.

d, a, t, v_i, v_f = Reals("d a t v__i v__f")

equations = [
    d == v_i * t + (a * t**2) / 2,
    v_f == v_i + a * t,
]
print("Kinematic equations:")
print(equations)

# Given v_i, v_f and a, find d
problem = [v_i == 30, v_f == 0, a == -8]
print("Problem:")
print(problem)

print("Solution:")
solve(equations + problem)

# Create two lists containing 5 integer variables
X = [Int("x%s" % i) for i in range(5)]
Y = [Int("y%s" % i) for i in range(5)]
Z = [Int(f"x{i}") for i in range(5)]
print(X)
print(Z)


# 9x9 matrix of integer variables
X = [[Int("x_%s_%s" % (i + 1, j + 1)) for j in range(9)] for i in range(9)]

# each cell contains a value in {1, ..., 9}
cells_c = [And(1 <= X[i][j], X[i][j] <= 9) for i in range(9) for j in range(9)]

# each row contains a digit at most once
rows_c = [Distinct(X[i]) for i in range(9)]

# each column contains a digit at most once
cols_c = [Distinct([X[i][j] for i in range(9)]) for j in range(9)]

# each 3x3 square contains a digit at most once
sq_c = [
    Distinct([X[3 * i0 + i][3 * j0 + j] for i in range(3) for j in range(3)])
    for i0 in range(3)
    for j0 in range(3)
]

sudoku_c = cells_c + rows_c + cols_c + sq_c

# sudoku instance, we use '0' for empty cells
instance = (
    (0, 0, 0, 0, 9, 4, 0, 3, 0),
    (0, 0, 0, 5, 1, 0, 0, 0, 7),
    (0, 8, 9, 0, 0, 0, 0, 4, 0),
    (0, 0, 0, 0, 0, 0, 2, 0, 8),
    (0, 6, 0, 2, 0, 1, 0, 5, 0),
    (1, 0, 2, 0, 0, 0, 0, 0, 0),
    (0, 7, 0, 0, 0, 0, 5, 2, 0),
    (9, 0, 0, 0, 6, 5, 0, 0, 0),
    (0, 4, 0, 9, 7, 0, 0, 0, 0),
)

instance_c = [
    If(instance[i][j] == 0, True, X[i][j] == instance[i][j])
    for i in range(9)
    for j in range(9)
]

s = Solver()
s.add(sudoku_c + instance_c)
if s.check() == sat:
    m = s.model()
    r = [[m.evaluate(X[i][j]) for j in range(9)] for i in range(9)]
    print_matrix(r)
else:
    print("failed to solve")
