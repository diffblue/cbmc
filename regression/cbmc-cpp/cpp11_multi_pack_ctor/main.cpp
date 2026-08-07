// N5008 [temp.variadic]/5,7,8: a constructor template with MULTIPLE
// template parameter packs, each deduced from a distinct
// class-template-id parameter plus a trailing function parameter pack
// -- the shape of libc++ __tuple_impl's five-pack constructor.  Four
// single-pack assumptions broke it (flat-argument surgery in
// deduction, positional pack re-binding in template_mapt::build, and
// two copies of the empty-pack parameter removal deleting the
// NON-empty pack's parameter too).  The assertion encodes all three
// pack arities (Uf=2, Ul=0, Up=2 -> 202).
extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned long size_t;
template <size_t...> struct idx {};
template <class...> struct types {};
struct S
{
  int total;
  template <size_t... Uf, class... Tf, size_t... Ul, class... Tl, class... Up>
  explicit S(idx<Uf...>, types<Tf...>, idx<Ul...>, types<Tl...>, Up &&... u)
    : total(static_cast<int>(sizeof...(Uf) * 100 + sizeof...(Ul) * 10 +
                             sizeof...(Up)))
  {
  }
};
int main()
{
  S s(idx<0, 1>(), types<int, int>(), idx<>(), types<>(), 1, 2);
  __CPROVER_assert(s.total == 202, "pack arities");
  return 0;
}
