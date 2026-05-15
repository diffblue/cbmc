// Translation unit where `struct Inner` is only forward-declared.
// This makes anonymous-tag identifiers inside `struct S` serialize
// differently from main.c's view, exercising the structural-equivalence
// path of the linker.

struct Inner;

struct S
{
  union
  {
    struct Inner *via_struct;
    int *via_int;
  } u;
  int sentinel;
};

int read_sentinel(struct S *p)
{
  return p->sentinel;
}
