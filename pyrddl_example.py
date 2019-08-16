from pyrddl.parser import RDDLParser

taxi_composite_filepath = "./taxi-rddl-domain/taxi-oo_mdp_composite_01.rddl"
recon_filepath = "./ipc2018-domains/original/cooperative-recon/cooperative-recon_mdp_composite.rddl"
recon_composite_filepath = "./ipc2018-domains/original/cooperative-recon/cooperative-recon_inst_mdp__01.rddl"
recon_domain_filepath = "./ipc2018-domains/original/cooperative-recon/cooperative-recon_mdp.rddl"
nav_filepath = "./misc-domains/nav.rddl"
# read RDDL file
with open(taxi_composite_filepath, 'r') as file:
    rddl = file.read()

# buid parser
parser = RDDLParser()
parser.build()

# parse RDDL
model = parser.parse(rddl) # AST
model.build()
print(model)

reward = model.domain.reward
cpfs = model.domain.cpfs
next_state_fluent_ordering = model.domain.next_state_fluent_ordering  #Need this to understand transition dynamics
pvariables = model.domain.pvariables
preconds = model.domain.preconds


#Looks like model.build() does this (ish)
    #NVM, that deals with rddl preconditions. We want to parse transitions to get skills
def construct_skills(cpfs,next_state_fluent_ordering):
    """
    :param cpfs:
    :param next_state_fluent_ordering:
    :return: list of (precondition,action,effect) triples
    """
    pass

def pyrddl_to_z3_condition(ast):
    """
    :param ast: pyrddl-style ast for a condition
    :return: z3-style ast for a condition
    """
    #Replace and, or, forall, exists with z3 equivalents
    pass

