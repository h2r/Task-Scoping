from typing import List
def foo() -> List[str]:
	return ['cat','soup']

a = foo()
for x in a: print(x)