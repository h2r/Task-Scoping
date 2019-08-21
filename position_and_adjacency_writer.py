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

if __name__ == "__main__":
	min_x, max_x, min_y, max_y = [0,4,0,4]
	r = get_rddl_str(min_x,max_x,min_y,max_y)
	print(r)