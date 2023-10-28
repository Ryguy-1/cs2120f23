from z3 import *

x, y = Reals('x y')
s = Solver()
s.add(x**2+y**2 == 1, )
s.check()
print(s.model())
print((-0.9921567416)**2+(1/8)**2)


x, y = Bools('x y')
