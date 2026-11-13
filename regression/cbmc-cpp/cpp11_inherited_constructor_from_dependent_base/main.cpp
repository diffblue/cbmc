extern "C" void __CPROVER_assert(bool, const char *);
struct traits
{
  int k;
};
template <class T, bool I, bool C>
struct translator_base
{
  explicit translator_base(const T &t) : traits_k(t.k)
  {
  }
  int traits_k;
};
// libstdc++'s _RegexTranslator: the constructor is inherited through a
// typedef that names the dependent base ([namespace.udecl]/3,
// [class.inhctor.init])
template <class T, bool I, bool C>
struct translator : translator_base<T, I, C>
{
  typedef translator_base<T, I, C> base;
  using base::base;
};
template <class T, bool I>
struct translator<T, I, false> : translator_base<T, I, false>
{
  typedef translator_base<T, I, false> base;
  using base::base;
  int partial() const
  {
    return 1;
  }
};
template <class T, bool I, bool C>
struct matcher
{
  typedef translator<T, I, C> trans;
  explicit matcher(const T &t) : tr(t)
  {
  }
  trans tr;
};
int main()
{
  traits t{7};
  matcher<traits, false, false> m(t);
  __CPROVER_assert(
    m.tr.traits_k == 7 && m.tr.partial() == 1, "partial specialization");
  matcher<traits, true, true> n(t);
  __CPROVER_assert(n.tr.traits_k == 7, "primary template");
  __CPROVER_assert(m.tr.traits_k == 8, "WRONG (must FAIL)");
}
