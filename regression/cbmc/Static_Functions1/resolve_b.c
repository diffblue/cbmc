// file-local f, distinct from resolve_a.c's static f and the global f
static int f(void)
{
  return 2;
}

int fb(void)
{
  return f();
}
