struct Inner
{
  int payload;
};

struct S
{
  union
  {
    struct Inner *via_struct;
    int *via_int;
  } u;
  int sentinel;
};

int read_payload(struct S *p)
{
  return *p->u.via_int;
}

int main(void)
{
  int value = 7;
  struct S s;
  s.u.via_int = &value;
  s.sentinel = 42;
  __CPROVER_assert(read_payload(&s) == 7, "read through the union");

  struct Inner inner = {8};
  s.u.via_struct = &inner;
  struct S *p = &s;
  __CPROVER_assert(*p->u.via_int == 8, "type-punned read");
  return 0;
}
