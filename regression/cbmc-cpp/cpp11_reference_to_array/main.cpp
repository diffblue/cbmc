// N5008 [dcl.init.ref]/5: a reference to an array type binds directly
// to an array lvalue of compatible type -- `int (&r)[3] = arr;` is
// direct binding, no array-to-pointer decay ([conv.array] applies only
// where a pointer is required).  CBMC rejects the initialization
// ("invalid implicit conversion from 'signed int [3]' to 'AR'") and,
// in template contexts, DROPS the reference when the argument is
// int(&)[3] (holder<int(&)[3]> instantiates with V = int[3]).
// This underlies the ranges pipe: take_view<int(&)[1]> must hold a
// reference-to-array; g++ and clang++ accept and run clean.
extern "C" void __CPROVER_assert(bool, const char *);
using AR = int (&)[3];
int main()
{
  int arr[3]{1, 2, 3};
  AR r = arr;
  __CPROVER_assert(r[2] == 3, "reference-to-array alias");
  int (&s)[3] = arr;
  __CPROVER_assert(s[0] == 1, "direct reference-to-array");
  return 0;
}
