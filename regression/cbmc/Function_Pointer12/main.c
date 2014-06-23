typedef void (ft)();

void foo()
{
}

// see ISO/IEC 9899:1999 page 199 clause 8
void zz(ft f1, ft *f2)
{
  assert(f1==foo);
  assert(f2==foo);
}

int main()
{
  zz(foo, foo);
}
