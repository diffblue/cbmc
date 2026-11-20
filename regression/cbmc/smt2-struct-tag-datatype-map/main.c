// Regression test for #9190: map::at crash in smt2_convt when
// find_symbols_rec discovers struct types through code-type (function
// pointer) parameter chains, causing datatype declarations to be emitted
// in the wrong order.
//
// The type chain that triggers the bug:
//   Wrapper -> FatPtr (direct member, struct_tag)
//            -> VTable (direct member, struct_tag)
//            -> fn_t (code type, function pointer)
//            -> Formatter* (parameter)
//            -> Formatter (direct member struct_tag(FatPtr))
//
// When FatPtr is in recstack (being processed), Formatter is discovered
// and its datatype declaration references FatPtr's sort before FatPtr
// has been declared.

struct Formatter;
typedef void (*fn_t)(struct Formatter *);
struct VTable
{
  fn_t callback;
};
struct FatPtr
{
  struct VTable vt;
  int data;
};
struct Formatter
{
  struct FatPtr ptr;
  int flag;
};
struct Wrapper
{
  struct FatPtr fp;
  int extra;
};

int main(void)
{
  struct Wrapper w;
  w.fp.data = __CPROVER_nondet_int();
  w.extra = __CPROVER_nondet_int();
  __CPROVER_assert(w.extra == 2, "nondeterministic");
  return 0;
}
