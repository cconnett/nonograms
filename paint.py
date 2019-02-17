import sys

import z3

rows = [(), (4,), (6,), (2, 2), (2, 2), (6,), (4,), (2,), (2,), (2,), ()]
columns = [(), (9,), (9,), (2, 2), (2, 2), (4,), (4,), ()]
## grid = [
##   z3.Bools(['({r}, {c})'.format(r=r,c=c)
##       for r in range(len(rows))]) for c in range(len(columns))]
#row_block_starts = Bools(['({r}, {c})'.format(r=r,c=c) for r in range(len(rows)) for c in range(len(columns))])
#column_block_starts = Bools(['({r}, {c})'.format(r=r,c=c) for r in range(len(rows)) for c in range(len(columns))])

s = z3.Solver()

grid = z3.Function('grid', z3.IntSort(), z3.IntSort(), z3.BoolSort())

blocks_by_row = [list() for r in range(len(rows))]
for r, row in enumerate(rows):
  if not row:
    for c in range(len(columns)):
      s.add(grid(r, c) == False)
    continue
  for i, clue in enumerate(row):
    block = z3.Int(f'{i}th block of {clue} in row {r}')
    blocks_by_row[r].append(block)
    s.add(0 <= block)
    s.add(block <= len(columns) - clue)
    # Tiles in the block are on.
    for offset in range(clue):
      s.add(grid(r, block + offset))
    # Before and after the block are off. Out-of-bounds isn't a problem.
    s.add(False == grid(r, block + clue))
    s.add(False == grid(r, block - 1))
  for i in range(len(blocks_by_row[r]) - 1):
    s.add(blocks_by_row[r][i + 1] > (blocks_by_row[r][i] + clue))

blocks_by_col = [list() for r in range(len(columns))]
for c, col in enumerate(columns):
  if not col:
    for r in range(len(rows)):
      s.add(grid(r, c) == False)
    continue
  for i, clue in enumerate(col):
    block = z3.Int(f'{i}th block of {clue} in column {c}')
    blocks_by_col[c].append(block)
    # Set the legal range for a block.
    s.add(0 <= block)
    s.add(block <= len(rows) - clue)
    # Tiles in the block are on.
    for offset in range(clue):
      s.add(grid(block + offset, c))
    # Before and after the block are off. Out-of-bounds isn't a problem.
    s.add(False == grid(block + clue, c))
    s.add(False == grid(block - 1, c))
  # Enforce ordering of the blocks.
  for i in range(len(blocks_by_col[c]) - 1):
    s.add(blocks_by_col[c][i + 1] > (blocks_by_col[c][i] + clue))

answer = s.check()
if answer != z3.sat:
  print(answer)
  sys.exit(0)

m = s.model()
# print(m)
b2 = [[m.eval(b) for b in row] for row in blocks_by_row]
print(b2)
for r in range(len(rows)):
  for c in range(len(columns)):
    if any(m.eval(b) == c for b in blocks_by_row[r]):
      print('▒▒', end='')
    elif m.eval(grid(r, c)):
      print('██', end='')
    else:
      print('  ', end='')
  print()
