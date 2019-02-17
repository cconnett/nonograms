import copy
import sys
import time

rows = []
columns = []
for line in sys.stdin:
  if 'c' in line:
    break
  rows.append(tuple(int(v) for v in line.split()))
for line in sys.stdin:
  columns.append(tuple(int(v) for v in line.split()))

def Legals(clues, offset, length):
  minimum = sum(clues) + len(clues) - 1
  if length - offset < minimum:
    return
  if not clues:
    yield ()
    return
  for i in range(offset, length):
    for element in Legals(clues[1:], i + clues[0] + 1, length):
      yield (i,) + element


def Expand(clues, configs, length):
  for config in configs:
    r = [False for _ in range(length)]
    for block, dist in zip(config, clues):
      for offset in range(dist):
        r[block + offset] = True
    yield r

work_rows = [
    list(Expand(row_clues, Legals(row_clues, 0, len(rows)), len(rows)))
    for row_clues in rows
]
work_cols = [
    list(Expand(col_clues, Legals(col_clues, 0, len(columns)), len(columns)))
    for col_clues in columns
]

truth_values = [[None] * len(columns) for _ in range(len(rows))]

old_truth = None
while True:
  if truth_values == old_truth:
    break
  old_truth = copy.deepcopy(truth_values)
  for r, wr in enumerate(work_rows):
    # Filter rows that conflict with truth values.
    for c, truth in enumerate(truth_values[r]):
      if truth is not None:
        for cand in wr:
          if cand[c] != truth:
            wr.remove(cand)
  for r, wr in enumerate(work_rows):
    for c in range(len(columns)):
      distincts = list(set(cand[c] for cand in wr))
      if len(distincts) == 1 and distincts[0] is not None:
        truth_values[r][c] = distincts[0]

  for c, wc in enumerate(work_cols):
    # Filter cols that conflict with truth values.
    for r in range(len(rows)):
      truth = truth_values[r][c]
      if truth is not None:
        for cand in wc:
          if cand[r] != truth:
            wc.remove(cand)
  for c, wc in enumerate(work_cols):
    for r in range(len(rows)):
      distincts = list(set(cand[r] for cand in wc))
      if len(distincts) == 1 and distincts[0] is not None:
        truth_values[r][c] = distincts[0]

  for r in range(len(rows)):
    for c in range(len(columns)):
      if truth_values[r][c] == True:
        print('██', end='')
      elif truth_values[r][c] == None:
        print('▒▒', end='')
      else:
        print('  ', end='')
    print()
  print('⎯⎯' * len(columns))

  time.sleep(1)
