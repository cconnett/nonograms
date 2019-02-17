import sys

import z3

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
    (4, 2, 1, 1, 2),  #
    (1, 1, 1, 1, 1, 2, 4),  #
    (4, 2, 4),  #
    (1, 1, 4, 1, 1, 1, 1, 1),  #
    (1, 4),
    (7, 2, 2, 1, 2, 2),
    (1, 1, 1, 1, 1, 1, 2),
    (1, 3, 1, 2, 3, 4),
    (1, 3, 1, 1, 3, 4),
    (1, 3, 1, 6, 1, 1),
    (1, 1, 1, 2, 1),
    (7, 1, 1, 2, 1, 3),
]

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

  last_block = blocks_by_row[r][-1]
  # Last block doesn't run off the grid.
  s.add(last_block <= len(columns) - last_block.clue)
  # Squares after the last block are off.
  for c in range(len(columns)):
    s.add(z3.Implies(c >= last_block + last_block.clue, grid(r, c) == False))

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

blocks_by_column = [list() for c in range(len(columns))]
for c, column in enumerate(columns):
  if not column:
    for r in range(len(rows)):
      s.add(grid(r, c) == False)
    continue
  # Make the blocks.
  for i, clue in enumerate(column):
    block = z3.Int(f'{i} block of {clue} in column {c}')
    block.clue = clue
    blocks_by_column[c].append(block)

  first_block = blocks_by_column[c][0]
  # First block is >= 0.
  s.add(first_block >= 0)
  # Squares before the first block are off.
  for r in range(len(rows)):
    s.add(z3.Implies(r < first_block, grid(r, c) == False))

  last_block = blocks_by_column[c][-1]
  # Last block doesn't run off the grid.
  s.add(last_block <= len(rows) - last_block.clue)
  # Squares after the last block are off.
  for r in range(len(rows)):
    s.add(z3.Implies(r >= last_block + last_block.clue, grid(r, c) == False))

  # Tiles in the block are on.
  for block in blocks_by_column[c]:
    for offset in range(block.clue):
      s.add(grid(block + offset, c))
  # Set invariants between pairs of adjacent blocks.
  for i in range(len(blocks_by_column[c]) - 1):
    current_block = blocks_by_column[c][i]
    next_block = blocks_by_column[c][i + 1]
    # The next block is sufficiently far after the current block.
    s.add(next_block > current_block + current_block.clue)
    # Squares between the end of the current block and the start of the next
    # block are off.
    for r in range(len(rows)):
      s.add(
          z3.Implies(
              z3.And(r >= current_block + current_block.clue, r < next_block),
              grid(r, c) == False))

answer = s.check()
if answer != z3.sat:
  print(answer)
  sys.exit(0)

m = s.model()

import pprint
pprint.pprint([[m.eval(b) for b in row] for row in blocks_by_row])
#pprint.pprint([[m.eval(b) for b in column] for column in blocks_by_column])

for r in range(len(rows)):
  for c in range(len(columns)):
    ## if any(m.eval(b) == c for b in blocks_by_row[r]):
    ##   print('██', end='')
    ##   # print('▒▒', end='')
    if m.eval(grid(r, c)):
      print('██', end='')
    else:
      print('  ', end='')
  print()
