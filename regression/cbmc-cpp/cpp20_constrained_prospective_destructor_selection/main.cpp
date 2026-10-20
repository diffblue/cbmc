extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [class.dtor]/4: overload resolution among the prospective
// destructors selects the one whose constraints are satisfied; the other's
// definition is not instantiated ([temp.inst]/4), so its call of the
// constrained destroy() is never checked for holder<int> (libc++'s
// std::expected::__repr)
int destroyed = 0;
struct nt;
template <class T>
constexpr bool trivial = true;
template <>
constexpr bool trivial<nt> = false;
template <class T>
struct holder
{
  T v;
  constexpr ~holder() requires(trivial<T>) = default;
  constexpr ~holder() requires(!trivial<T>)
  {
    destroy();
  }

private:
  void destroy() requires(!trivial<T>)
  {
    ++destroyed;
  }
};
struct nt
{
  ~nt()
  {
  }
};
int main()
{
  {
    holder<int> h{1};
    __CPROVER_assert(h.v == 1, "trivial");
  }
  {
    holder<nt> n{};
  }
  __CPROVER_assert(destroyed == 1, "non-trivial destroyed once");
  __CPROVER_assert(destroyed == 2, "WRONG (must FAIL)");
  return 0;
}
