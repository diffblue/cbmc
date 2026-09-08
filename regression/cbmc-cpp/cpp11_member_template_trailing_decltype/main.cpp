// Dog-food kernel (src/util/options.cpp to_json family), reduced
// round-85 from 45 header-dependent lines to 26 header-free ones: a
// member function template whose TRAILING RETURN TYPE dereferences a
// data member of CLASS type (`auto map(F f) const -> decltype(f(*b_))`
// with b_ a user iterator, [dcl.fct]/12 + [dcl.type.decltype]) fails
// to resolve ("found no match for symbol 'map'").  With a raw POINTER
// member it works (t1/t2/t5 negatives); the USER operator* is
// load-bearing.
// Round-85 diagnosis: during guess_function_template_args'
// typecheck_type of the trailing decltype, the member operator*
// resolution reaches cpp_typecheck_fargst::match with ops=2 (the
// implied itert object DUPLICATED) against operator*($constthis)'s 1
// parameter -- arity mismatch, candidate dropped, sfinae-suppressed.
// Outside deduction the same expression resolves with ops=1.  The
// object-duplication site was not identified (probe trail in the
// findings log, round 85).
extern "C" void __CPROVER_assert(bool, const char *);
struct pr
{
  int first, second;
};
struct itert
{
  pr *p_;
  pr &operator*() const
  {
    return *p_;
  }
};
template <class It> struct ranget
{
  It b_;
  template <class F> auto map(F f) const -> decltype(f(*b_))
  {
    return f(*b_);
  }
};
int main()
{
  pr arr[1] = {{1, 21}};
  ranget<itert> r{itert{arr}};
  int v = r.map([](const pr &p) { return 2 * p.second; });
  __CPROVER_assert(v == 42, "trailing decltype through class iterator");
  return 0;
}
