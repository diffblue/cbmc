extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
concept pointer_like = requires(T p)
{
  *p;
};
// a requires-expression whose body is a single compound requirement with a
// type-constraint
template <class T>
concept has_begin = requires(T & t)
{
  {
    t.begin()
    } -> pointer_like;
};
struct range
{
  int *begin();
};
static_assert(has_begin<range>, "member begin() returning a pointer");
static_assert(!has_begin<int>, "int has no member begin()");
int main()
{
  __CPROVER_assert(!has_begin<int>, "not satisfied for int");
  __CPROVER_assert(has_begin<int>, "WRONG (must FAIL)");
}
