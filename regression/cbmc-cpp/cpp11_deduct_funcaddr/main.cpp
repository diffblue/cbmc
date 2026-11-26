// Per [temp.deduct.funcaddr]: when a function template specialization
// is the target of a context that requires a specific function type,
// template arguments are deduced from that target type.  A common use
// is passing the address of a function template to a typed context.

// A function template.
template <class T>
int id_sum(T a, T b)
{
  return a + b;
}

// A function that takes a pointer to a function-of-(int,int)-returning-int.
int apply(int (*f)(int, int), int x, int y)
{
  return f(x, y);
}

int main()
{
  // The address of id_sum<T> is in a context that expects
  //   int (*)(int, int)
  // so T must be deduced as int.
  int r = apply(&id_sum, 3, 4);
  __CPROVER_assert(r == 7, "template deduced from function pointer type");

  // Without the ampersand: same deduction applies (function-to-pointer
  // conversion).
  int r2 = apply(id_sum, 5, 6);
  __CPROVER_assert(r2 == 11, "template deduced without explicit &");

  return 0;
}
