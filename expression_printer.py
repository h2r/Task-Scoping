import re

def collapse_whitespace(s):
    rex = re.compile(r'\s+')
    return rex.sub(' ', s)
def get_matching_parens(s):
    paren_pairs = []
    left_parens_stack = []
    for i, c in enumerate(s):
        if c == "(":
            left_parens_stack.append(i)
        if c == ")":
            if len(left_parens_stack) == 0:
                raise ValueError(f"Unbalanced Parens: {i}")
            paren_pairs.append((left_parens_stack.pop(), i))
    if len(left_parens_stack) > 0:
        raise ValueError(f"Extra left parens: {left_parens_stack}")
    return sorted(paren_pairs, key=lambda x: x[0])
def overlapping(a,b):
    # Make sure a comes first
    if a[0] > b[0]:
        a_ = a
        a = b
        b = a_
        del a_
    if a[1] >= b[0]:
        return True
    else:
        return False
def range_contain(a,b):
    return a[0] <= b[0] and a[1] >= b[1]

def get_maximal_ranges(ranges):
    ranges = sorted(ranges, key=lambda x: x[0])
    maximals = []
    for r in ranges:
        add_r = True
        for m in maximals:
            if range_contain(m,r):
                add_r = False
                continue
            elif range_contain(r,m):
                maximals.pop(m)
        if add_r:
            maximals.append(r)
    return maximals
def index_complement(s, subtracted_ranges):
    # Assumes that subtracted_ranges are non overlapping
    subtracted_ranges = sorted(subtracted_ranges, key=lambda x: x[0])
    new_ranges = []
    start = 0
    for r in subtracted_ranges:
        if r[0] > start:
            new_ranges.append((start, r[0]))
        start = r[1] + 1
    if start < len(s):
        new_ranges.append((subtracted_ranges[-1][1], len(s)))
    return new_ranges

def parse_operators(s):
    maximal_paren_pairs = get_maximal_ranges(get_matching_parens(s))
    # paren_guts_idxs = [(a+1,b) for (a,b) in maximal_paren_pairs]
    str_ranges = index_complement(s, maximal_paren_pairs)
    assert len(maximal_paren_pairs) == len(str_ranges)
    ret = []
    for i in range(len(maximal_paren_pairs)):
        op_range = str_ranges[i]
        op = s[op_range[0]:op_range[1]]
        arg_range = maximal_paren_pairs[i]
        arg_s = s[arg_range[0] + 1:arg_range[1]]
        arg = parse_operators(arg_s)
        ret.append((op, arg))
    return ret

s = """And(And(Not(in-taxi(curly, t0)),
        Not(in-taxi(smoov, t0)),
        Not(in-taxi(edison, t0)),
        Not(in-taxi(isbell, t0))))"""
s = collapse_whitespace(s)

parse_operators(s)