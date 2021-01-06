struct bar
{
  char *ptr;
};

static struct bar foo __attribute__((used))
__attribute__((__section__(".ref.data")));

static struct bar foo __attribute__((used))
__attribute__((__section__(".ref.data"))) = {0};

void use_foo()
{
  __CPROVER_assert(foo.ptr == 0, "null");
}
