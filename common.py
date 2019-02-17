def ReadNono(stream):
  rows = []
  columns = []
  for line in stream:
    if 'c' in line:
      break
    rows.append(tuple(int(v) for v in line.split()))
  for line in stream:
    columns.append(tuple(int(v) for v in line.split()))
  return rows, columns

def Print(truth):
  print('\x1b[2J')
  print('⎯⎯' * len(truth))
  for r in range(len(truth)):
    for c in range(len(truth[r])):
      if truth[r][c] == True:
        print('██', end='')
      elif truth[r][c] == None:
        print('▒▒', end='')
      else:
        print('  ', end='')
    print()
  print('⎯⎯' * len(truth))
