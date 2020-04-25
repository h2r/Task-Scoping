import z3


n_passengers = 2
Passenger, passengers = z3.EnumSort("Passenger", [f"p{i}" for i in range(n_passengers)])
p = z3.Const("p", Passenger)
assert type(p) == z3.z3.DatatypeRef
# What is z3.z3.FuncDeclRef? What is the point of the constructor?
# assert Passenger.constructor(0).name() == "p0"
# assert type(Passenger.constructor(0)) == z3.z3.FuncDeclRef
assert type(passengers[0]) == z3.z3.DatatypeRef
# for i in range(n_passengers): assert Passenger.constructor(i) == passengers[i]

# Passenger = z3.DeclareSort("Passenger")
# passengers = [z3.Const(f"p{i}", Passenger) for i in range(n_passengers)]

Taxi, taxis = z3.EnumSort("Taxi", ["t0"])
t = z3.Const("t", Taxi)
# taxi = z3.Const("taxi", Taxi)
# p0 = z3.Const("p0",Passenger)
# print(Passenger)
# print(type(z3.Int('z')))
# print(type(z3.IntSort()))
# z3.Const()
for pi in passengers: print(pi)
passenger_x = z3.Function("passenger-y-curr", Passenger, z3.IntSort())
in_taxi = z3.Function("passenger-in-taxi", Passenger, Taxi, z3.BoolSort())

print(in_taxi(passengers[0], taxis[0]))

print(in_taxi(p, t))

errbody_inside = z3.ForAll([p,t], in_taxi(p,t))
print(errbody_inside)

taxi_empty = z3.ForAll([p,t], z3.Not(in_taxi(p,t)))
print(taxi_empty)

