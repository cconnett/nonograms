import copy
import sys
import time

import common


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
    yield tuple(r)


def SolveIteratively(rows, columns):
  work_rows = [
      set(Expand(row_clues, Legals(row_clues, 0, len(columns)), len(columns)))
      for row_clues in rows
  ]
  work_cols = [
      set(Expand(col_clues, Legals(col_clues, 0, len(rows)), len(rows)))
      for col_clues in columns
  ]

  truth_values = [[None] * len(columns) for _ in range(len(rows))]
  while True:
    old_count = sum(map(len, work_cols)) + sum(map(len, work_rows))
    old_truth = copy.deepcopy(truth_values)
    intermediate_truth = copy.deepcopy(truth_values)
    for r, wr in enumerate(work_rows):
      # Filter rows that conflict with truth values.
      for c, truth in enumerate(truth_values[r]):
        if truth is not None:
          smaller_wr = wr.copy()
          for cand in wr:
            if cand[c] != truth:
              smaller_wr.remove(cand)
          work_rows[r] = smaller_wr
      new_count = sum(map(len, work_cols)) + sum(map(len, work_rows))
    # Find squares that have only a single possible truth value.
    for r, wr in enumerate(work_rows):
      for c in range(len(columns)):
        seen = set()
        for cand in wr:
          seen.add(cand[c])
          if len(seen) > 1:
            break
        else:
          truth_values[r][c] = next(iter(seen))
      if truth_values != intermediate_truth:
        intermediate_truth = copy.deepcopy(truth_values)
        common.Print(truth_values)
        print(f'\x1b[A\x1b[KConsidering {new_count} configurations.')
        time.sleep(.18)

    for c, wc in enumerate(work_cols):
      # Filter cols that conflict with truth values.
      for r in range(len(rows)):
        truth = truth_values[r][c]
        if truth is not None:
          smaller_wc = wc.copy()
          for cand in wc:
            if cand[r] != truth:
              smaller_wc.remove(cand)
          work_cols[c] = smaller_wc
      new_count = sum(map(len, work_cols)) + sum(map(len, work_rows))
    # Find squares that have only a single possible truth value.
    for c, wc in enumerate(work_cols):
      for r in range(len(rows)):
        seen = set()
        for cand in wc:
          seen.add(cand[r])
          if len(seen) > 1:
            break
        else:
          truth_values[r][c] = next(iter(seen))
      if truth_values != intermediate_truth:
        intermediate_truth = copy.deepcopy(truth_values)
        common.Print(truth_values)
        print(f'\x1b[A\x1b[KConsidering {new_count} configurations.')
        time.sleep(.18)
    new_count = sum(map(len, work_cols)) + sum(map(len, work_rows))
    if old_count == new_count and old_truth == truth_values:
      if new_count > len(rows) + len(columns):
        print("I'm stuck.")
      break
    old_count = new_count
    old_truth = copy.deepcopy(truth_values)


if __name__ == '__main__':
  try:
    SolveIteratively(*common.ReadNono(open(sys.argv[1])))
  except Exception as e:
    import pdb
    pdb.post_mortem()
