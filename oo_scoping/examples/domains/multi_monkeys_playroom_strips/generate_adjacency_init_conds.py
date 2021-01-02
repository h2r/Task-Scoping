init_conds_str = ''
grid_limit = 10
for x1 in range(1,grid_limit):
    init_conds_str += f"(adjacent-x x{x1} x{x1+1})\n(adjacent-x x{x1+1} x{x1})\n"

for y1 in range(1,grid_limit):
    init_conds_str += f"(adjacent-y y{y1} y{y1+1})\n(adjacent-y y{y1+1} y{y1})\n"
    
print(init_conds_str)
