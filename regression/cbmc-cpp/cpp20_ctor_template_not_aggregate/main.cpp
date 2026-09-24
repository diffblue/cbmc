// N5008 [dcl.init.aggr]/1: a class with a user-declared constructor
// TEMPLATE is not an aggregate -- braced initialisation calls the template.
extern "C" void __CPROVER_assert(bool, const char *);

template <typename R>
struct ref
{
  R *p;
  template <typename T>
  requires(!__is_same(T, ref)) constexpr ref(T &&t)
    : p(&static_cast<R &>(static_cast<T &&>(t)))
  {
  }
  constexpr R &base() const
  {
    return *p;
  }
};

template <typename R>
ref(R &) -> ref<R>;

struct ref_int
{
  int *p;
  template <typename T>
  ref_int(T &t) : p(&t)
  {
  }
};

int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  // explicit specialization, braced
  ref<int[5]> r1{arr};
  __CPROVER_assert(r1.base()[2] == 3, "braced, explicit args");
  // explicit specialization, parenthesised
  ref<int[5]> r2(arr);
  __CPROVER_assert(r2.base()[4] == 5, "parenthesised");
  // deduction guide, braced temporary
  auto r3 = ref{arr};
  static_assert(__is_same(decltype(r3), ref<int[5]>), "guide");
  __CPROVER_assert(r3.base()[0] == 1, "guide value");
  int i = 7;
  ref_int ri{i};
  __CPROVER_assert(*ri.p == 7, "non-template class");
  __CPROVER_assert(r1.base()[1] == 3, "WRONG (must FAIL)");
  return 0;
}
