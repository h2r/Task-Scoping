flip_bit = False
f = open('prob-09-expers.txt', 'r')
for line in f:
    if flip_bit and 'real' in line:
        print(line[7:-2])
    flip_bit = not(flip_bit)
