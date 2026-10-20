extern "C" void __CPROVER_assert(bool, const char *);
template <class It, class Se>
inline void destroy(It first, Se last) noexcept;
template <class T>
void use(T *p)
{
  destroy(p, p + 1);
}
// N5008 [dcl.fct]/5, [temp.over.link]/6: the top-level const of a parameter
// is not part of the function type, so this definition is the one of the
// template declared above (the MSVC STL's _Destroy_range)
template <class It, class Se>
inline void destroy(It first, const Se last) noexcept
{
  *first = 7;
}
int main()
{
  int x = 0;
  use(&x);
  __CPROVER_assert(x == 7, "definition used");
  __CPROVER_assert(x == 0, "WRONG (must FAIL)");
  return 0;
}
