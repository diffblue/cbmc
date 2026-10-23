extern "C" void __CPROVER_assert(bool, const char *);
struct choice_t
{
  int size;
};
struct cpo
{
  template <class T>
  static constexpr choice_t choice = {sizeof(T)};
  // N5008 [temp.constr.atomic]/3, [expr.const]/5: the atomic constraint
  // reads a member of a constexpr static data member template of class
  // type, a constant expression (the MSVC STL's range access customization
  // point objects: `requires (_Choice<_Ty &>._Strategy != _St::_None)')
  template <class T>
  requires(choice<T>.size == 1) static int call(T)
  {
    return 1;
  }
  static int call(...)
  {
    return 2;
  }
};
int main()
{
  __CPROVER_assert(
    cpo::call('a') == 1 && cpo::call(1) == 2, "constraint decided");
  __CPROVER_assert(cpo::call(1) == 1, "WRONG (must FAIL)");
  return 0;
}
