int nondet_int();

int Test = nondet_int();

int f()
{
  return 1;
}

// this is _not_ ANSI-C!
int g=f();

int main()
{
  assert(g==1);
}
