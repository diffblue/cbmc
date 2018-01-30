int main()
{
  __CPROVER_integer a, b;
  a=0;
  b=a;
  b++;
  b*=100;
  __CPROVER_assert(0, "");
}
