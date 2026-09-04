// N5008 [dcl.meaning.general]/1 + [dcl.array] + [dcl.init.ref]/5: in
// `T (D)[N]` the parenthesized declarator applies ON TOP of the array
// type: `int (&r)[3]` declares a reference to an array (direct
// binding, no decay) and `int (*p)[3]` a pointer to one.  CBMC's
// declarator parser dropped the parenthesized inner declarator for
// ARRAY postfixes (only the function postfix composed it), so the
// "reference" silently COPIED the array (wrong code: writes through it
// did not alias) and pointer-to-array initialization failed to
// convert.  Also [dcl.type.auto.deduct]/4: plain `auto` deduced from
// an array must DECAY to a pointer to its first element.
extern "C" void __CPROVER_assert(bool, const char *);
using AR = int (&)[3];
template <class T, int N> auto ret(T (&t)[N])
{
  return t;
}
int main()
{
  int arr[3]{1, 2, 3};
  AR r = arr;
  __CPROVER_assert(r[2] == 3, "reference-to-array alias");
  int(&s)[3] = arr;
  __CPROVER_assert(s[0] == 1, "direct reference-to-array");
  s[0] = 42;
  __CPROVER_assert(arr[0] == 42, "reference aliases the array");
  int(*p)[3] = &arr;
  (*p)[1] = 9;
  __CPROVER_assert(arr[1] == 9, "pointer-to-array aliases");
  __CPROVER_assert(ret(arr) == arr, "auto return decays to same address");
  return 0;
}
