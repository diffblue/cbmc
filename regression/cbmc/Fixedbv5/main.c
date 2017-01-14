int main()
{
  typedef __CPROVER_fixedbv[32][16] ft;
  ft a, b;

  __CPROVER_assume(a==1 || a==(ft)0.5 || a==2 || a==3 || a==(ft)0.25);
  b=a;
  a/=2;
  a*=2;
  __CPROVER_assert(a==b, "fixedbv div works");
}
