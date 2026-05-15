// [temp.deduct.conv]/1 with [temp.deduct.conv]/3: when A is not a
// reference, the pointer/array transformations on P apply.
//
// Here the conversion-function template's return type (P) is a
// pointer-to-T; the destination (A) is `int*`.  Per the deduction
// rules, T is deduced as `int` and the conversion operator is
// instantiated as `operator int*()`.

struct holder
{
  int storage[3];

  template <class T>
  operator T *()
  {
    return storage;
  }
};

int main()
{
  holder h;
  h.storage[0] = 1;
  h.storage[1] = 2;
  h.storage[2] = 3;

  int *p = h;
  __CPROVER_assert(p[0] == 1, "deduce T = int via operator T*");
  __CPROVER_assert(p[1] == 2, "deduce T = int via operator T*");
  __CPROVER_assert(p[2] == 3, "deduce T = int via operator T*");

  return 0;
}
