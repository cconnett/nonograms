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
  # Make the blocks.
  for i, clue in enumerate(row):
    block = z3.Int(f'{i} block of {clue} in row {r}')
    block.clue = clue
    blocks_by_row[r].append(block)

  first_block = blocks_by_row[r][0]
  # First block is >= 0.
  s.add(first_block >= 0)
  # Squares before the first block are off.
  for c in range(len(columns)):
    s.add(z3.Implies(c < blocks_by_row[r][0], grid(r, c) == False))

  # Last block doesn't run off the grid.
  last_block = blocks_by_row[r][-1]
  s.add(last_block <= len(columns) - last_block.clue)
  # Squares after the last block are off.
  for c in range(len(columns)):
    s.add(z3.Implies(c > last_block + last_block.clue, grid(r, c) == False))

  # Tiles in the block are on.
  for block in blocks_by_row[r]:
    for offset in range(block.clue):
      s.add(grid(r, block + offset))
  # Set invariants between pairs of adjacent blocks.
  for i in range(len(blocks_by_row[r]) - 1):
    current_block = blocks_by_row[r][i]
    next_block = blocks_by_row[r][i + 1]
    # The next block is sufficiently far after the current block.
    s.add(next_block > current_block + current_block.clue)
    # Squares between the end of the current block and the start of the next
    # block are off.
    for c in range(len(columns)):
      s.add(
          z3.Implies(
              z3.And(c >= current_block + current_block.clue, c < next_block),
              grid(r, c) == False))

## blocks_by_col = [list() for r in range(len(columns))]
## for c, col in enumerate(columns):
##   if not col:
##     for r in range(len(rows)):
##       s.add(grid(r, c) == False)
##     continue
##   for i, clue in enumerate(col):
##     block = z3.Int(f'{i} block of {clue} in column {c}')
##     blocks_by_col[c].append(block)
##     # Set the legal range for a block.
##     s.add(0 <= block)
##     s.add(block <= len(rows) - clue)
##     # Tiles in the block are on.
##     for offset in range(clue):
##       s.add(grid(block + offset, c))
##     # Before and after the block are off. Out-of-bounds isn't a problem.
##     s.add(False == grid(block + clue, c))
##     s.add(False == grid(block - 1, c))
##   # Enforce ordering of the blocks.
##   for i in range(len(blocks_by_col[c]) - 1):
##     s.add(blocks_by_col[c][i + 1] > (blocks_by_col[c][i] + clue))

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
