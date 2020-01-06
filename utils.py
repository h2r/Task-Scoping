import z3
import re
from instance_building_utils import g2n_names

# def get_var_names(expr):
# 	vars = [str(i) for i in z3.z3util.get_vars(expr)]
# 	return vars
def grounded_att2objects(att_str):
	"""
	:param att_name: name of attribute. ex. "passenger-in-taxi(passenger1,taxi0)"
	:return: list of object names. ex. ["passenger1", "taxi0"]
	"""
	r = re.compile("[(),]")
	split_str = r.split(att_str)
	split_str = [x for x in split_str if x != ""]
	if len(split_str) > 1:
		return split_str[1:]
	else: return []
#
#
#
# def test_grounded_att2objects(silent=False):
# 	att_name = "att"
# 	object_names = ["x0", "x1"]
# 	for i in range(len(object_names) + 1):
# 		object_names_true = object_names[:i]
# 		att_str = g2n_names(att_name,object_names_true[:i])
# 		# print("Input str:\n{}".format(att_str))
# 		object_names_emp = grounded_att2objects(att_str)
# 		assert object_names_true == object_names_emp, str(object_names_emp)
# 	if not silent: print("")
def condition_str2objects(prop_str_list):
	if isinstance(prop_str_list, str):
		prop_str_list = [prop_str_list]
	objects = []
	for prop_str in prop_str_list:
		paren_groups = re.findall("\(([^()]*)\)",prop_str)
		for p in paren_groups:
			split_p = p.spgilit(",")
			objects += split_p
	objects = list(set(objects))
	objects.sort()
	return objects
# TODO make condition_str2vars().
def condition_str2objects_test():
	prop_str = "synth_Or(Not(PASSENGERS_YOU_CARE_FOR(p0)),\nAnd(Not(passenger-in-taxi(p0,t0)),\npassenger-x-curr(p0) == PASSENGER_GOAL_X(p0),passenger-y-curr(p0) == PASSENGER_GOAL_Y(p0)))"
	objects = condition_str2objects(prop_str)
	print(objects)
if __name__ == "__main__":
	# test_grounded_att2objects("grounded_att2objects passed tests")
	condition_str2objects_test()