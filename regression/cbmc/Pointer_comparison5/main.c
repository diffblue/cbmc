int main()
{
  int A[2];
  int b;

  int *ptr = &A[1];

  if(ptr == &b)
  {
    __CPROVER_assert(0, "unreachable");
  }
  else if((unsigned long long)ptr == (unsigned long long)&b)
  {
    __CPROVER_assert(0, "unreachable");
  }
}
