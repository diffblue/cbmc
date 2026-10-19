extern "C" void __CPROVER_assert(bool, const char *);
struct table
{
  long operator[](int) const
  {
    return 0;
  }
};
// N5008 [expr.sizeof]/1, [over.sub]/1: in `sizeof(t[0])' the operand is a
// subscript expression, here a call of table::operator[] (a shape of the
// MSVC STL's ranges concepts)
template <class T>
constexpr bool subscript_is_long = sizeof(T{}[0]) == sizeof(long);
int main()
{
  table t;
  __CPROVER_assert(
    sizeof(t[0]) == sizeof(long) && subscript_is_long<table>,
    "operator[] result");
  __CPROVER_assert(sizeof(t[0]) == sizeof(char), "WRONG (must FAIL)");
  return 0;
}
