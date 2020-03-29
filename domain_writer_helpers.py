try:
    import textwrap
    textwrap.indent
except AttributeError:  # undefined function (wasn't added until Python 3.3)
    def indent(text, amount, ch=' '):
        padding = amount * ch
        return ''.join(padding+line for line in text.splitlines(True))
else:
    def indent(text, amount, ch=' '):
        return textwrap.indent(text, amount * ch)

def num2str(n):
	ones = n % 10
	tens = n - ones
	return "{}{}".format(tens, ones)
def make_adjacency_statements(xpositions, ypositions):
	#For each x, add left(x,x+1) and right(x,x-1)
	adjacency_strings = []
	for x_id in range(len(xpositions)):
		if x_id != 0:
			adjacency_strings.append("ADJACENT_RIGHT({}, {});".format(xpositions[x_id],xpositions[x_id-1]))
		if x_id != len(xpositions) - 1:
			adjacency_strings.append("ADJACENT_LEFT({}, {});".format(xpositions[x_id],xpositions[x_id+1]))
	for y_id in range(len(xpositions)):
		if y_id != 0:
			adjacency_strings.append("ADJACENT_UP({}, {});".format(ypositions[y_id],ypositions[y_id-1]))
		if y_id != len(xpositions) - 1:
			adjacency_strings.append("ADJACENT_DOWN({}, {});".format(ypositions[y_id],ypositions[y_id+1]))
	result = "\n".join(adjacency_strings)
	return result

def get_position_lists(min_x,max_x,min_y,max_y):
	xpositions = ["x{}".format(num2str(x)) for x in range(min_x,max_x+1)]
	ypositions = ["y{}".format(num2str(x)) for x in range(min_x,max_x+1)]
	return xpositions, ypositions
def get_rddl_str(min_x,max_x,min_y,max_y):
	"""
	:param min_x:
	:param max_x:
	:param min_y:
	:param max_y:
	:return: rddl str stuff
	"""
	xpositions, ypositions = get_position_lists(min_x,max_x,min_y,max_y)
	adjacency_string = make_adjacency_statements(xpositions,ypositions)
	print(xpositions)
	xpos_str = "xpos               : {{ {}}};".format(",".join(xpositions))
	ypos_str = "ypos               : {{ {}}};".format(",".join(ypositions))
	result = "\n".join([xpos_str,ypos_str,adjacency_string])
	return result

def get_in_taxi_str(num_passengers, num_taxis):
	template_str = "passenger-in-taxi(p{}, t{}) = false;"
	result_list = []
	for t_id in range(num_taxis):
		for p_id in range(num_passengers):
			result_list.append(template_str.format(p_id,t_id))
	result = "\n".join(result_list)
	return result

def taken_no_courses():
	courses = ["c0000", "c0001", "c0002", "c0003", "c0004", "c0100", "c0101", "c0102", "c0103", "c0200", "c0201", "c0202", "c0300", "c0301", "c0302"]
	program_req_strings = []

	not_taken_strings = []
	for c in courses:
		not_taken_strings.append("~passed({});".format(c))
		program_req_strings.append("~PROGRAM_REQUIREMENT({});".format(c))
	not_taken = "\n".join(not_taken_strings)
	not_required = "\n".join(program_req_strings)
	not_prereq_strings = []
	for c0 in courses:
		for c1 in courses:
			if c0 != c1:
				not_prereq_strings.append("~PREREQ({}, {});".format(c0,c1))
	not_prereq = "\n".join(not_prereq_strings)
	print(not_taken)
	print(not_prereq)
	print(not_required)

def door_opening():
	buttons = ["b0", "b1"]
	doors = ["d0", "d1", "d2"]
	for d in doors[1:]:
		for b in buttons:
			print(f"opens({b}, {d}) = false;")
	for d in doors:
		for d2 in doors:
			if d != d2:
				for b in buttons:
					print(f"opens-conditionally({b}, {d}, {d2}) = false;")
	for d in doors:
		print(f"door-open({d}) = false;")

def enumerated_move(numbers = tuple(range(2))):

	def n2s(i): return f"@{i}"
	def make_action_lines(condition, pvar, obj, step_func):
		lines = []
		for i in numbers:
			i2 = step_func(i)
			if i2 in numbers:
				s = f"if (({condition}) & ({pvar}({obj}) == {n2s(i)}))\n\tthen {n2s(i2)}"
				lines.append(s)
		result = "\nelse ".join(lines)
		return result
	def increment(i): return i + 1
	def decrement(i): return i - 1
	def make_taxi_cpfs(): #Too  much code duplication.
		actions = ["move_west", "move_east"]
		step_funcs = [decrement, increment]
		parts = []
		for i in range(2):
			parts.append(make_action_lines(actions[i], "taxi-x", "?t", step_funcs[i]))
		taxi_x_cpf = "taxi-x'(?t) =\n" + indent("\nelse ".join(parts),4) + ";"

		actions = ["move_north", "move_south"]
		step_funcs = [increment, decrement]
		parts = []
		for i in range(2):
			parts.append(make_action_lines(actions[i], "taxi-y", "?t", step_funcs[i]))
		taxi_y_cpf = "taxi-y'(?t) =\n" + indent("\nelse ".join(parts),4) + ";"
		result = taxi_x_cpf + "\n\n" + taxi_y_cpf
		return result
	def make_passenger_cpfs():
		actions = ["move_west", "move_east"]
		step_funcs = [decrement, increment]
		parts = []
		for i in range(2):
			condition = actions[i] + " & exists_{ ?t : taxi } [ passenger-in-taxi( ?p, ?t ) ]"
			parts.append(make_action_lines(condition, "passenger-x-curr", "?p", step_funcs[i]))
		passenger_x_cpf = "passenger-x-curr'(?p) =\n" + indent("\nelse ".join(parts),4) + ";"

		actions = ["move_north", "move_south"]
		step_funcs = [increment, decrement]
		parts = []
		for i in range(2):
			condition = actions[i] + " & exists_{ ?t : taxi } [ passenger-in-taxi( ?p, ?t ) ]"
			parts.append(make_action_lines(condition, "passenger-y-curr", "?p", step_funcs[i]))
		passenger_y_cpf = "passenger-y-curr'(?p) =\n" + indent("\nelse ".join(parts), 4) + ";"
		result = passenger_x_cpf + "\n\n" + passenger_y_cpf
		return result
	taxi_cpfs = make_taxi_cpfs()
	passenger_cpfs = make_passenger_cpfs()
	result = indent("\n\n".join([taxi_cpfs,passenger_cpfs]),4)
	print(result)
	return result
if __name__ == "__main__":
	# min_x, max_x, min_y, max_y = [0,4,0,4]
	# r = get_rddl_str(min_x,max_x,min_y,max_y)
	# print(r)
	# in_taxi_str = get_in_taxi_str(2,1)
	# print(in_taxi_str)
	# taken_no_courses()
	# door_opening()
	enumerated_move()