from pyrddl.parser import RDDLParser
import collections

def make_triplet_dict(rddl_file_location='/home/nishanth/Documents/IPC_Code/rddlsim/files/taxi-rddl-domain/taxi-oo_simple.rddl'):
    # read RDDL file
    with open(rddl_file_location, 'r') as file:
        rddl = file.read()

    # buid parser
    parser = RDDLParser()
    parser.build()

    # parse RDDL
    model = parser.parse(rddl) # AST

    actions_list = model.domain.action_fluents.keys()
    #print(actions_list)

    # print(type(model.domain.cpfs[1]))
    action_to_precond_to_effect = collections.defaultdict(dict)

    for state_variable_cpf in model.domain.cpfs[1]:
        if(state_variable_cpf.expr.etype[0] == 'control'):
            for action_precondition in state_variable_cpf.expr._expr[1]:
                for action in actions_list:
                    if action in action_precondition.scope:
                        print(state_variable_cpf.name.replace("'", ""))
                        action_to_precond_to_effect[action][action_precondition._expr] = state_variable_cpf.name.replace("'", "")

    print('BREAK!')

    return action_to_precond_to_effect

    # IMPORTANT!!!
    # This parser will only work for a transition function that begins with if statements for every block
    # Further, every block needs to contain statements with only one action
