#include <stdlib.h>

union value
{
  short halves[2];
  int whole;
};

struct cell
{
  char kind;
  union value v;
};

struct cell table[3];

int main()
{
  unsigned row, col;
  __CPROVER_assume(row < 3 && col < 2);

  // a write into an array inside a union member, at non-constant indices
  table[row].v.halves[1 - col] = 5;
  table[row].v.halves[col] = 7;
  __CPROVER_assert(table[row].v.halves[col] == 7, "written");
  __CPROVER_assert(table[row].v.halves[1 - col] == 5, "other half kept");
  __CPROVER_assert(table[row].kind == 0, "other member kept");
  __CPROVER_assert(
    table[row].v.whole == (col == 0 ? 0x50007 : 0x70005), "whole");

  // likewise for an array of non-constant size on the heap
  unsigned count;
  __CPROVER_assume(count > 0 && count < 4);
  struct cell *cells = malloc(count * sizeof(struct cell));
  __CPROVER_assume(cells != NULL);
  cells->v.halves[col] = 9;
  __CPROVER_assert(cells->v.halves[col] == 9, "written on the heap");

  return 0;
}
