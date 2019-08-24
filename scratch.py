from typing import List, Tuple, Dict
def foo() -> Dict['str','str']:
	return {"cat":"dog"}
a = foo()
for x in a: print(x)