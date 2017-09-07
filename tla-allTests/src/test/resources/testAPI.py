from z3 import *

fname = "test.smt2"
#f = file(fname,"r")

s = Solver()


s.add( parse_smt2_file( fname ) )

print(s.check())
print(s.model())
