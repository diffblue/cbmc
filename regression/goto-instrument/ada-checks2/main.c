void __CPROVER_Ada_Overflow_Check(int condition)
{
}

int main()
{
  int i = 0;
  __CPROVER_Ada_Overflow_Check(i > 5);
  return 0;
}
