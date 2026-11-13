// N5008 [temp.deduct.type]/2: every deduction of a template parameter must
// give the same type, cv-qualifiers included.  CBMC compared the deduced
// types with their qualifiers stripped, so T = const char (from T *) and
// T = char (from T) were taken as consistent.  [temp.deduct.call]/2 still
// ignores the top-level cv-qualifiers of an argument type.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
int two(T, T)
{
  return 1;
}
template <class T>
int refval(const T &, T)
{
  return 1;
}
template <class T>
int ptrs(T *, T *)
{
  return 1;
}
template <class T>
struct box
{
};
template <class T>
int boxes(box<T>, T)
{
  return 1;
}
int two(...)
{
  return 2;
}
int ptrs(...)
{
  return 2;
}
template <class T>
int f(T *, T)
{
  return 1;
}
int f(...)
{
  return 2;
}
int main()
{
  const char s[] = "x";
  int *p = nullptr;
  __CPROVER_assert(f(s, 'x') == 2, "const char vs char conflicts");
  __CPROVER_assert(f(p, 1L) == 2, "int vs long conflicts");
  __CPROVER_assert(f(p, 1) == 1, "consistent");
  const int c = 1;
  volatile int v = 2;
  int i = 3;
  const int *pc = &c;
  int *pi = &i;
  __CPROVER_assert(two(c, i) == 1, "top-level const ignored");
  __CPROVER_assert(two(v, i) == 1, "top-level volatile ignored");
  __CPROVER_assert(refval(c, i) == 1, "const T & and T");
  __CPROVER_assert(ptrs(pc, pi) == 2, "const int * and int * conflict");
  __CPROVER_assert(ptrs(pc, pc) == 1, "const int * twice");
  const box<int> b{};
  __CPROVER_assert(boxes(b, c) == 1, "class template argument and const");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
