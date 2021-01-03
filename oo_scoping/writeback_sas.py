# TODO! Prune the initial and goal condition sections!!!!
# Right now, you've just pruned the variable definitions and 
# operator sections...
def writeback_scoped_sas(rel_ops, rel_pvars, problem_file_path):
    """
    Function that writes out a scoped SAS+ problem file

    :param rel_ops - a set of strings of the names of all the relevant operators
    :param rel_pvars - a set of strings of all the relevant pvars
    :param problem_file_path - a string representing the path to the written SAS+ file

    Output: (void), just writes out the file

    """
    scoped_domain_lines = []
    skip_lines = False
    with open(problem_file_path, "r") as f:
        sas_domain_lines = f.readlines()
        i_line = 0
        while i_line < len(sas_domain_lines):
            # The line below 'end_metric' is the number of state variables in the 
            # problem, so write this out there.
            if "end_metric" in sas_domain_lines[i_line]:
                scoped_domain_lines.append(sas_domain_lines[i_line])
                scoped_domain_lines.append(str(len(rel_pvars))+'\n')
                i_line += 2
            elif "begin_variable" in sas_domain_lines[i_line]:
                # If the next line after a begin_variable statement is
                # not in the rel_pvars set, then just keep skipping lines until
                # you hit the next end_line
                if sas_domain_lines[i_line + 1][:-1] not in rel_pvars:
                    skip_lines = True
                else:
                    scoped_domain_lines.append(sas_domain_lines[i_line])
                i_line += 1
            elif "end_variable" in sas_domain_lines[i_line] and skip_lines:
                # If skip_lines is true and you see 'end_variable', start appending
                # from the next line onwards
                skip_lines = False
                i_line += 1
            elif "begin_operator" in sas_domain_lines[i_line]:
                # If the next line after a begin_variable statement is
                # not in the rel_ops set, then just keep skipping lines until
                # you hit the next end_line
                if sas_domain_lines[i_line + 1][:-1] not in rel_ops:
                    skip_lines = True
                else:
                    scoped_domain_lines.append(sas_domain_lines[i_line])
                i_line += 1
            elif "end_operator" in sas_domain_lines[i_line] and skip_lines:
                # If skip_lines is true and you see 'end_operator', start appending
                # from the next line onwards
                skip_lines = False
                i_line += 1
            else:
                if not skip_lines:
                    scoped_domain_lines.append(sas_domain_lines[i_line])
                i_line += 1

    # The filepath will always be <file_name>.sas at the end, so create a file
    # named <file_name>_scoped.sas
    with open(problem_file_path[:-4]+'_scoped'+problem_file_path[-4:],'w+') as f_scoped:
        f_scoped.writelines(scoped_domain_lines)
