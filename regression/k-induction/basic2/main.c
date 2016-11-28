int main()
{
  int a=0, b=0;

  while(a<=10 && b<=10)
  {
    int choice;

    b++;
    a=b;

    // this is 2-inductive, but not 1-inductive
    __CPROVER_assert(a>=0, "property");
  }
}
