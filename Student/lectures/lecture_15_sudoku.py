from z3 import *

# Sudoku -- other authorship, Z3 Python API document

# The following example encodes the sudoku problem in Z3.
# Different sudoku instances can be solved by modifying
# the matrix instance. This example makes heavy use of
# list comprehensions available in the Python programming
# language.

print("Sudoku")

# 9x9 matrix of integer variables
X = [[Int(f"x_{i+1}_{j+1}") for j in range(9)] for i in range(9)]

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

# constraints on cell values: fixed where given otherwise unconstrained
instance_c = [
    If(instance[i][j] == 0, True, X[i][j] == instance[i][j])
    for i in range(9)
    for j in range(9)
]

# Let's see the additional constraints
print("Instance_c", instance_c)

# Create a general solver
s = Solver()

# Add rules for Sudoku and constraints from instance
s.add(sudoku_c + instance_c)

# And try to solve
if s.check() == sat:
    m = s.model()
    r = [[m.evaluate(X[i][j]) for j in range(9)] for i in range(9)]
    print_matrix(r)
else:
    print("failed to solve")
