def g2n_builder(attributes):
	"""
	:param attributes: a list of DomainAttribute and DomainAction objects
	:return: a function that takes in an attribute name and a list of object ids and returns a str
	"""
	att2args = {}
	for a in attributes:
		att2args[a.name] = a.arguments
	def g2n(att_name, object_ids):
		object_names =[]
		for i in range(len(object_ids)):
			object_type = att2args[att_name][i]
			object_names.append(type_and_id2name(object_type,object_ids[i]))
		return g2n_names(att_name,object_names)
	return g2n
def type_and_id2name(object_type, object_id):
	return "{}{}".format(object_type,object_id)
def g2n_names(att_name, object_names):
	name = att_name + "(" + ",".join([str(i) for i in object_names]) + ")"
	return name
def g2v_builder(var_dict, g2n):
	def g2v(att_name, object_ids):
		return g2v_need_dict(att_name,object_ids,var_dict, g2n)
	return g2v

def g2v_need_dict(att_name, object_ids, var_dict,g2n):
	return var_dict[g2n(att_name, object_ids)]

def object_counts_to_names(object_counts):
	object_names = {}
	for k, v in object_counts.items():
		object_names[k] = [str(i) for i in range(v)]
	return object_names

