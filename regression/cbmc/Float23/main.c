int main()
{
  float a, b;
  __CPROVER_assert((a>b)==(a-b>0), "theorem");
}
