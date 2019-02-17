import copy
import sys

#rows = [(7,), (1, 1), (1, 3, 1), (1, 3, 1), (1, 3, 1), (1, 1), (7,)]
#columns = [(7,), (1, 1), (1, 3, 1), (1, 3, 1), (1, 3, 1), (1, 1), (7,)]
rows = [
    (7, 1, 2, 7),
    (1, 1, 3, 1, 1),
    (1, 3, 1, 2, 2, 1, 3, 1),
    (1, 3, 1, 1, 1, 1, 3, 1),
    (1, 3, 1, 1, 1, 1, 3, 1),
    (1, 1, 1, 1, 1),
    (7, 1, 1, 1, 7),
    (2, 2),
    (3, 8, 2, 1),
    (3, 1, 2, 2, 2, 1),
    (1, 1, 1, 2, 1, 1, 1),
    (1, 4, 2, 5, 1),
    (1, 2, 1, 1, 1, 1, 2),
    (1, 2, 1, 6),
    (7, 1, 1, 2, 1, 1),
    (1, 1, 2, 3, 2, 1),
    (1, 3, 1, 1, 1, 2, 1, 2),
    (1, 3, 1, 2, 1, 4),
    (1, 3, 1, 3, 1, 3, 1),
    (1, 1, 1, 1, 4, 2),
    (7, 1, 1, 1, 1, 1, 1),
]
columns = [
    (7, 4, 7),
    (1, 1, 2, 1, 1),
    (1, 3, 1, 2, 1, 1, 3, 1),
    (1, 3, 1, 3, 1, 3, 1),
    (1, 3, 1, 1, 1, 1, 3, 1),
    (1, 1, 2, 2, 1, 1),
    (7, 1, 1, 1, 7),
    (2, 1),
    (1, 4, 6, 3),
    (4, 2, 1, 1, 2),
    (1, 1, 1, 1, 1, 2, 4),
    (4, 2, 4),
    (1, 1, 4, 1, 1, 1, 1, 1),
    (1, 4),
    (7, 2, 2, 1, 2, 2),
    (1, 1, 1, 1, 1, 1, 2),
    (1, 3, 1, 2, 3, 4),
    (1, 3, 1, 1, 3, 4),
    (1, 3, 1, 6, 1, 1),
    (1, 1, 1, 2, 1),
    (7, 1, 1, 2, 1, 3),
]


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


try:
  print(list(Expand(rows[0], Legals(rows[0], 0, 21), 21)))
  # print(list(Legals(rows[0], 0, 21)))
except:
  import pdb
  pdb.post_mortem()

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
