// Regression test for structural-equivalence-aware linker.
//
// Two translation units share the same C type `struct S`, but the irept
// representations of `S` differ at the byte level because the inner type
// `struct Inner` is COMPLETE in this TU and INCOMPLETE in module.c.
// CBMC's compile-time canonicalisation bakes that completion state into
// any anonymous-tag identifiers that transitively reference Inner; the
// linker used to flag this as a "conflicting function declarations" warning
// and produce 'pointer parameter types differ between declaration and
// definition' diagnostics.
//
// With the structural-equivalence-aware needs_renaming_type / duplicate_
// type_symbol pair, the linker recognises the two `struct S` types as the
// same C type and merges them silently.

struct Inner
{
  int payload;
};

struct S
{
  // Anonymous union whose synthetic tag identifier serializes Inner's
  // completion state, making the byte-level encoding of S differ between
  // this TU (Inner complete here) and module.c (Inner forward-declared
  // there).
  union
  {
    struct Inner *via_struct;
    int *via_int;
  } u;
  int sentinel;
};

int read_sentinel(struct S *p);

int main(void)
{
  struct Inner inner = {7};
  struct S s;
  s.u.via_struct = &inner;
  s.sentinel = 42;
  __CPROVER_assert(read_sentinel(&s) == 42, "sentinel survived linking");
  return 0;
}
