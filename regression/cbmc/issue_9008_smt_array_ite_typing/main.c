// Regression test for https://github.com/diffblue/cbmc/issues/9008
//
// CBMC used to emit ill-typed SMT-LIB 2 of the form
//   (select (ite cond <bit-vector> <bit-vector>) <index>)
// when convert_index was applied to an array-typed if_exprt whose two
// branches were both encoded as bit-vectors (the common case being a
// member access of a struct that is read out of memory as a flat
// bit-vector).  Conforming SMT-LIB 2 solvers reject this with messages
// such as "select expects array operand" / "array select operating on
// non-array".
//
// The conditional pointer dereference below keeps the if_exprt from
// being lifted into the surrounding indexing expression by the
// simplifier, so that convert_index is invoked on an array-typed
// if_exprt whose branches are bit-vector encodings of mat_t.

typedef struct
{
  int row[4];
} row_t;

typedef row_t mat_t[4];

int main(void)
{
  mat_t A, B;
  int cond;
  unsigned x, i;
  __CPROVER_assume(x < 4 && i < 4);

  mat_t *p = cond ? &A : &B;
  int v = (*p)[x].row[i];

  __CPROVER_assert(v == 0, "may fail");
  return 0;
}
