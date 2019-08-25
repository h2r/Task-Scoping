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

if __name__ == "__main__":
	# test_grounded_att2objects("grounded_att2objects passed tests")
	pass