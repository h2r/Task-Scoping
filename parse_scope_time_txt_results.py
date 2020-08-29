f = open('prob-09-expers.txt', 'r')
for line in f:
    if 'time' in line:
        print(line[12:17])
