try:
	import textwrap

	textwrap.indent
except AttributeError:  # undefined function (wasn't added until Python 3.3)
	def indent(text, amount, ch=' '):
		padding = amount * ch
		return ''.join(padding + line for line in text.splitlines(True))
else:
	def indent(text, amount, ch=' '):
		return textwrap.indent(text, amount * ch)

def n2s(i): return f"@{i}"
def p2s(p): return f"p{p}"

def make_movement_cdfs(numbers=tuple(range(2))):

	def make_action_lines(condition, pvar, obj, step_func):
		lines = []
		for i in numbers:
			i2 = step_func(i)
			if i2 in numbers:
				s = f"if (({condition}) & ({pvar}({obj}) == {n2s(i)}))\n\tthen {n2s(i2)}"
				lines.append(s)
		# lines.append(f"{pvar}({obj})")
		result = "\nelse ".join(lines)
		return result

	def increment(i):
		return i + 1

	def decrement(i):
		return i - 1

	def make_taxi_cpfs():  # Too  much code duplication.
		actions = ["move_west", "move_east"]
		step_funcs = [decrement, increment]
		parts = []
		for i in range(2):
			parts.append(make_action_lines(actions[i], "taxi-x", "?t", step_funcs[i]))
		taxi_x_cpf = "taxi-x'(?t) =\n" + indent("\nelse ".join(parts) + "\nelse taxi-x(?t);", 4)
		# taxi_x_cpf += "\nelse taxi-x(?t)"

		actions = ["move_north", "move_south"]
		step_funcs = [increment, decrement]
		parts = []
		for i in range(2):
			parts.append(make_action_lines(actions[i], "taxi-y", "?t", step_funcs[i]))
		taxi_y_cpf = "taxi-y'(?t) =\n" + indent("\nelse ".join(parts) + "\nelse taxi-y(?t);", 4)
		# taxi_y_cpf += "\nelse taxi-y(?t);"
		result = taxi_x_cpf + "\n\n" + taxi_y_cpf
		return result

	def make_passenger_cpfs():
		actions = ["move_west", "move_east"]
		step_funcs = [decrement, increment]
		parts = []
		for i in range(2):
			condition = actions[i] + " & exists_{ ?t : taxi } [ passenger-in-taxi( ?p, ?t ) ]"
			parts.append(make_action_lines(condition, "passenger-x-curr", "?p", step_funcs[i]))
		passenger_x_cpf = "passenger-x-curr'(?p) =\n" + indent("\nelse ".join(parts) + "\nelse passenger-x-curr(?p);",
															   4)
		# passenger_x_cpf += "\nelse passenger-x-curr(?p);"

		actions = ["move_north", "move_south"]
		step_funcs = [increment, decrement]
		parts = []
		for i in range(2):
			condition = actions[i] + " & exists_{ ?t : taxi } [ passenger-in-taxi( ?p, ?t ) ]"
			parts.append(make_action_lines(condition, "passenger-y-curr", "?p", step_funcs[i]))
		passenger_y_cpf = "passenger-y-curr'(?p) =\n" + indent("\nelse ".join(parts) + "\nelse passenger-y-curr(?p);",
															   4)
		# passenger_y_cpf += "\nelse passenger-y-curr(?p);"
		result = passenger_x_cpf + "\n\n" + passenger_y_cpf
		return result

	taxi_cpfs = make_taxi_cpfs()
	passenger_cpfs = make_passenger_cpfs()
	result = indent("\n\n".join([taxi_cpfs, passenger_cpfs]), 8)
	# print(result)
	return result

def write_domain_and_instance(grid_size=5, num_passengers=1):
	# Write domain
	with open("domain_template.txt",'r') as f:
		domain_template = f.read()

	numbers_strings = [n2s(i) for i in range(grid_size)]
	numbers_string = "{ " + ", ".join(numbers_strings) + " }"
	domain_template = domain_template.replace("!PUT NUMBERS HERE!",numbers_string)

	domain_template = domain_template.replace("!PUT MAX NUMBER HERE!",numbers_strings[-1])

	movement_cdfs = make_movement_cdfs(numbers = tuple(range(grid_size)))
	domain_template = domain_template.replace("!PUT MOVEMENT CDFS HERE!",movement_cdfs)
	domain_output_name = f"enum-taxi-domain-gridsize-{grid_size}.rddl"
	with open(domain_output_name, 'w') as f:
		f.write(domain_template)

# 	Write Instance

	with open("instance_template.txt",'r') as f:
		instance_template = f.read()
	instance_template = instance_template.replace("!PUT MAX NUMBER HERE!",numbers_strings[-1])
	instance_template = instance_template.replace("!PUT GRIDSIZE HERE!",str(grid_size))
	instance_template = instance_template.replace("!PUT NUM PASSENGERS HERE!",str(num_passengers))
	passenger_strings = [p2s(i) for i in range(num_passengers)]
	passenger_string = "{ " + ", ".join(passenger_strings) + " }"
	instance_template = instance_template.replace("!PUT PASSENGERS HERE!",passenger_string)
	instance_output_name = f"enum-taxi-inst-gridsize-{grid_size}-passengers-{num_passengers}.rddl"
	with open(instance_output_name,'w') as f:
		f.write(instance_template)


def write_many_domain_and_instances():
	grid_size = 5
	for num_passengers in range(43,101,3):
		write_domain_and_instance(grid_size=grid_size,num_passengers=num_passengers)
if __name__ == "__main__":
	# make_movement_cdfs()
	# write_domain_and_instance()
	write_many_domain_and_instances()