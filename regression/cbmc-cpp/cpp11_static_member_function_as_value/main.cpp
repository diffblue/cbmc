extern "C" void __CPROVER_assert(bool, const char *);
typedef int (*compare)(const void *, const void *);
typedef int (*unary)(int);
struct sorter
{
  static int by_value(const void *a, const void *b)
  {
    return *(const int *)a - *(const int *)b;
  }
  static int twice(int x)
  {
    return 2 * x;
  }
  static int counter;
  // a static member function as a value: cast, named through `this', and
  // through an object
  compare get() const
  {
    return (compare)by_value;
  }
  unary via_this()
  {
    this->counter = 3;
    return this->twice;
  }
  unary via_object()
  {
    return (*this).twice;
  }
};
int sorter::counter = 0;
int main()
{
  sorter s;
  int a = 5, b = 3;
  __CPROVER_assert(s.get()(&a, &b) == 2, "cast");
  __CPROVER_assert(s.via_this()(4) == 8 && sorter::counter == 3, "this->");
  __CPROVER_assert(s.via_object() == &sorter::twice, "(*this).");
  unary u = s.twice;
  __CPROVER_assert(u(1) == 2, "object.");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
