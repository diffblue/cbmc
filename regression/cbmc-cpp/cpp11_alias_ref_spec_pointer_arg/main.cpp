// N5008 [temp.deduct.type]/8: a reference pattern `T&` in a partial
// specialization is matched only by a reference argument.  CBMC's
// disambiguate_template_classes matcher stripped the `&` and deduced
// T=int* from a plain `int*` argument, selecting decay_<T&> for
// decay_<int*>, so the alias resolved to `int` and the initialization
// below failed ("invalid implicit conversion from 'signed int *'").
// Distilled (13 lines) from libc++'s __decay_t in the
// std::__to_address(reverse_iterator) return-type chain (the cpp20
// vector-family blocker).
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct decay_
{
  typedef T type;
};
template <class T>
struct decay_<T &>
{
  typedef T type;
};
template <class T>
using decay_t_ = typename decay_<T>::type;

int main()
{
  int x = 41;
  decay_t_<int *> a = &x;
  __CPROVER_assert(*a == 41, "decay_t_<int*> is int*");
  decay_t_<int &> b = 7;
  __CPROVER_assert(b == 7, "decay_t_<int&> is int");
  return 0;
}
