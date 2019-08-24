def get_hardcoded_triplet_dict(domain_name):
	if domain_name == "2buttons3atts":
		triplet_dict = collections.defaultdict(lambda: collections.defaultdict(list))
		buttons = ["b0","b1"]
		for b in buttons:
			action = instance_building_utils.g2n_names("toggle-button",[b])
			pvar_names = ['att{}'.format(i) for i in range(3)]
			effects = []
			for p in pvar_names:
				effects.append(instance_building_utils.g2n_names(p,[b]))
			triplet_dict[action] = effects
	else:
		raise ValueError("No hardcoded triplet_dict for domain: {}".format(domain_name))