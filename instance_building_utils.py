def g2n(att_name, object_ids):
	name = att_name + "_" + "_".join([str(i) for i in object_ids])
	return name
def g2v_builder(var_dict):
	def g2v(att_name, object_ids):
		return g2v_need_dict(att_name,object_ids,var_dict)
	return g2v

def g2v_need_dict(att_name, object_ids, var_dict):
	return var_dict[g2n(att_name, object_ids)]

def object_counts_to_names(object_counts):
	object_names = {}
	for k, v in object_counts.items():
		object_names[k] = [str(i) for i in range(v)]
	return object_names