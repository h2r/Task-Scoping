import z3
from classes import Skill
from utils import get_atoms, get_possible_values
import itertools

n_passengers = 3
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
passenger_y = z3.Function("passenger-y-curr", Passenger, z3.IntSort())
taxi_y = z3.Function("taxi-y-curr", Taxi, z3.IntSort())
in_taxi = z3.Function("passenger-in-taxi", Passenger, Taxi, z3.BoolSort())

print(in_taxi(passengers[0], taxis[0]))

print(in_taxi(p, t))

errbody_inside = z3.ForAll([p,t], in_taxi(p,t))
print(errbody_inside)

taxi_empty = z3.ForAll([p,t], z3.Not(in_taxi(p,t)))
print(taxi_empty)


north_w_p = Skill(in_taxi(p, t), "move_north()", [taxi_y(t), passenger_y(p)])
print(north_w_p)

# print(north_w_p.get_targeted_variables())
# passenger_y(p).children()

north_w_p_not_1 = Skill(z3.And(in_taxi(p,t),p!=passengers[1]), "move_north()", [taxi_y(t), passenger_y(p)])
assert north_w_p_not_1.get_targeted_variables()[1].decl() == passenger_y
print(north_w_p_not_1)
# tgt_objects = get_atoms(*north_w_p_not_1.get_targeted_variables())
# print(f"tgt_objects: {tgt_objects}")
# pcnd_objects = get_atoms(north_w_p_not_1.get_precondition())
# print(f"pcnd_objects: {pcnd_objects}")
possible_passengers = get_possible_values([north_w_p_not_1.get_precondition()], p)
print(possible_passengers)
possible_taxis = get_possible_values([north_w_p_not_1.get_precondition()], t)
print(possible_taxis)
possible_grounding_args = itertools.product(possible_passengers, possible_taxis)
for x in possible_grounding_args: print(in_taxi(*x))
print(f"Generic pvar: {north_w_p_not_1.get_targeted_variables()[1]}")
print("Grounded pvar:")
for x in possible_passengers:
	pvar_gnd = north_w_p_not_1.get_targeted_variables()[1].decl()(x)
	print(pvar_gnd)
gnd_effects = north_w_p_not_1.get_targeted_variables(grounded=True)
print("grounded_effects: ")
for e in gnd_effects: print(e)