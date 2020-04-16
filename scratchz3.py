import z3

p0_intaxi = z3.Bool('passenger-in-taxi(p0,t0)')
p1_intaxi = z3.Bool('passenger-in-taxi(p1,t0)')
taxi_y = z3.Int('taxi-y(t0)')
p0_y = z3.Int('passenger-y-curr(p0)')
p1_y = z3.Int('passenger-y-curr(p1)')

tempty = z3.And(z3.Not(p0_intaxi),z3.Not(p1_intaxi))
p0out = z3.Or(tempty, z3.And(z3.Not(p0_intaxi),p1_intaxi))
print(p0out)
print("\n")
x = z3.simplify(p0out)
print(x)
print()
print(z3.simplify(z3.Or(True,p0_intaxi)))