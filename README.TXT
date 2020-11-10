To run: Use python 3.7.9 (other versions may work)
pip install -r requirements.txt
python scoping_cli.py <domain_path> <problem_path>
    Example: python pddl_scoper.py "examples/multi_monkeys_playroom copy/multi_monkeys_playroom.pddl" "examples/multi_monkeys_playroom copy/prob-02.pddl"
The scoped domain and problem will be placed in the same directories as the input domain and problem. Use the scoped problem that ends with "with_cl". The file that says "sans_cl" may remove some causally-linked objects that, in principle, can be ignored, but due to limitations of PDDL we cannot always remove them safely.
Run your planner on the scoped pddl files
?
Profit