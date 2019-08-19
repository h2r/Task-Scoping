from pyrddl.parser import RDDLParser
from pyrddl_inspector import make_triplet_dict
import scoping

taxi_composite_filepath = "./taxi-rddl-domain/taxi-oo_mdp_composite_01.rddl"
recon_composite_filepath = "./ipc2018-domains/original/cooperative-recon/cooperative-recon_inst_mdp__01.rddl"
nav_filepath = "./misc-domains/nav.rddl"
structured_taxi_filepath = './taxi-rddl-domain/taxi-structured-composite_01.rddl'

# read RDDL file
with open(structured_taxi_filepath, 'r') as file:
    rddl = file.read()

# buid parser
parser = RDDLParser()
parser.build()

# parse RDDL
model = parser.parse(rddl) # AST
triplet_dict = make_triplet_dict(model=model)
skill_triples = scoping.triplet_dict_to_triples(triplet_dict)
print(skill_triples)