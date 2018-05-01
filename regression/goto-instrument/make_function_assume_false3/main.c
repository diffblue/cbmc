void function_a(int *num)
{
 *num = *num+1;
}

int main()
{
  int b=0;
  int c;
  if(c)
    function_a(&b);
  __CPROVER_assert(b!=0, "");
}