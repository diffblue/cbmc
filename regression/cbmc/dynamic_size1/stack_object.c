struct S
{
  __CPROVER_size_t size;
  char *p;
};

void func(struct S *s)
{
  char *p = s->p;
  __CPROVER_size_t size = __CPROVER_OBJECT_SIZE(p);
  __CPROVER_assert(size == s->size, "size ok");
  p[80] = 123; // should be safe
}

int main()
{
  __CPROVER_size_t buffer_size;
  __CPROVER_assume(buffer_size >= 100);
  char buffer[buffer_size];
  struct S s;
  s.size = buffer_size;
  s.p = buffer;
  func(&s);
}
