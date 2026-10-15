// file-local f, distinct from resolve_b.c's static f and the global f
static int f(void)
{
  return 1;
}

int fa(void)
{
  return f();
}
