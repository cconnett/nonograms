def ReadNono(stream):
  rows = []
  columns = []
  active = []  # Throw-away
  for line in stream:
    if 'columns' in line:
      active = columns
    elif 'rows' in line:
      active = rows
    elif not line:
      continue
    else:
      try:
        active.append(tuple(int(v) for v in line.split(',')))
      except ValueError:
        pass
  print(f'Read width {len(columns)} by height {len(rows)}')
  return rows, columns

def Print(truth):
  print('\x1b[2J')
  print('⎯⎯' * len(truth[0]))
  for r in range(len(truth)):
    for c in range(len(truth[r])):
      if truth[r][c] == True:
        print('██', end='')
      elif truth[r][c] == None:
        print('▒▒', end='')
      else:
        print('  ', end='')
    print()
  print('⎯⎯' * len(truth[0]))
  print()
