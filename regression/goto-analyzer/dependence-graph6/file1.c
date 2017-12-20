extern int s1;
static void sub(void)
{
  if (s1) {
  }
}

void f1(void)
{
  sub();
}
