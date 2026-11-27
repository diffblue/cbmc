typedef __builtin_va_list va_list;

// C23 va_start(ap), as GCC 15 and Clang 21 implement it
int c23_one(int n, ...)
{
  va_list ap;
  __builtin_c23_va_start(ap);
  int x = __builtin_va_arg(ap, int);
  __builtin_va_end(ap);
  return x;
}

// C23 va_start(ap, ...) ignores any argument other than ap
int c23_two(char c, int n, ...)
{
  va_list ap;
  __builtin_c23_va_start(ap, c);
  int x = __builtin_va_arg(ap, int);
  __builtin_va_end(ap);
  return x;
}

// C23 va_start(ap, ...) as GCC 13 and 14 and Clang 16 to 20 implement it
int c23_zero(char c, ...)
{
  va_list ap;
  __builtin_va_start(ap, 0);
  int x = __builtin_va_arg(ap, int);
  __builtin_va_end(ap);
  return x;
}

// GCC and Clang also start after the last named parameter when the second
// argument of __builtin_va_start is a different one (and warn about it)
int not_last(int a, int b, ...)
{
  va_list ap;
  __builtin_va_start(ap, a);
  int x = __builtin_va_arg(ap, int);
  __builtin_va_end(ap);
  return x;
}

int main()
{
  __CPROVER_assert(c23_one(1, 42) == 42, "c23_one");
  __CPROVER_assert(c23_two('a', 1, 42) == 42, "c23_two");
  __CPROVER_assert(c23_zero('a', 42) == 42, "c23_zero");
  __CPROVER_assert(not_last(1, 2, 42) == 42, "not_last");
  return 0;
}
