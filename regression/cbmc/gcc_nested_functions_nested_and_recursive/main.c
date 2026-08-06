// Pins two currently-working but previously-untested shapes:
//  * a nested function defined inside another nested function (exercising the
//    LIFO nested_function_context_stack), and
//  * a recursive nested function.
int main(void)
{
  // nested-in-nested
  int outer(int a)
  {
    int inner(int b)
    {
      return b * 2;
    }

    return inner(a) + 1;
  }

  // recursive nested function
  int fact(int n)
  {
    if(n <= 1)
      return 1;
    return n * fact(n - 1);
  }

  __CPROVER_assert(outer(3) == 7, "nested-in-nested result");
  __CPROVER_assert(fact(4) == 24, "recursive nested function result");

  return 0;
}
