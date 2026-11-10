// KNOWNBUG (N5008 [temp.inst]/2, [basic.lookup.qual], [temp.point]).
//
// A *namespace-scope* typedef of a qualified member type of a class-template
// instance -- `typedef std::vector<int>::iterator iter_t;` -- must resolve
// just as it does inside a function body or for a namespace-scope variable of
// the same type.  Naming `std::vector<int>::iterator` requires `vector<int>` to
// be implicitly instantiated ([temp.inst]/2), which at C++20 elaborates its
// `reverse_iterator` member typedef and thus the iterator-concept chain
// (`iterator_traits` -> `__cpp17_iterator` -> `copyable`/`movable`/`swappable`
// -> the `std::ranges::swap` CPO) for `__gnu_cxx::__normal_iterator`.
//
// DIVERGENCE: in the namespace-scope qualified-name resolution context that
// concept/CPO evaluation raises an uncontained failure that aborts resolution,
// so the typedef is never created (`symbol ... is unknown` / `CONVERSION
// ERROR`).  The identical use inside a function body, and a namespace-scope
// `std::vector<int>` variable, both succeed -- so this is a context-dependent
// instantiation divergence (the same family as std::string s("ab"), where the
// concept chain truncates basic_string).
//
// This is intentionally a small program over the real libstdc++ <vector>; a
// self-contained reproduction was not found because the failure depends on the
// exact structure of `__gnu_cxx::__normal_iterator` (Container template
// parameter + iterator_traits indirection + converting constructor) that
// faithful hand mimics do not trigger.
//
// When fixed, reclassify this test to CORE.

#include <vector>

typedef std::vector<int>::iterator iter_t;

int main()
{
  iter_t it{};
  (void)it;
  __CPROVER_assert(
    true, "namespace-scope vector<int>::iterator typedef elaborated");
  return 0;
}
