// N5008 [temp.inst]/2: constructing a temporary of a class template
// specialization is a context that requires a completely-defined type and thus
// implicitly instantiates the specialization.  Here std::pair<DS, DS> is
// constructed explicitly.  g++/clang++ compile this and p.first/p.second hold
// the constructor arguments, so p.first.no == 5.
//
// Regression: when a class (R) has a member std::unordered_map<DS, DS>, the
// libstdc++ hashtable machinery references std::pair<DS, DS> (distinct from the
// map's value_type std::pair<const DS, DS>) from within a typedef that is
// type-checked with elaboration suppressed (cpp_typecheckt::
// skip_typechecking_elaborate, set around typedef typechecking in
// cpp_typecheck_declaration.cpp).  That leaves std::pair<DS, DS> registered but
// INCOMPLETE.  The fix elaborates such an incomplete instance at the
// construction site (in cpp_typecheck_resolvet::resolve, before
// make_constructors) so its constructors are found; previously only the
// implicit members of an incomplete class were found ("found no match for
// symbol 'pair'").  The trigger requires a converting constructor (here
// DS(const std::string &)) that makes the trait evaluation reference the
// non-const std::pair<DS, DS>, and is include-order sensitive (<unordered_map>
// before <string>).
//
// This is the root of the goto-cc cascade on rename_symbol.cpp /
// replace_symbol.cpp (std::unordered_map<irep_idt, irep_idt> members).
// assertion.2 must FAIL, proving assertion.1 is non-vacuous.

#include <unordered_map>
#include <string>

struct DS
{
  unsigned no;
  DS() : no(0)
  {
  }
  DS(const std::string &) : no(2)
  {
  }
  bool operator==(const DS &o) const
  {
    return no == o.no;
  }
};

namespace std
{
template <>
struct hash<DS>
{
  std::size_t operator()(const DS &d) const
  {
    return d.no;
  }
};
} // namespace std

extern "C" void __CPROVER_assert(int, const char *);

// The member unordered_map<DS, DS> triggers the incomplete registration of
// std::pair<DS, DS>.
struct R
{
  std::unordered_map<DS, DS> m;
};

int main()
{
  R r;
  (void)r;
  DS a, b;
  a.no = 5;
  b.no = 9;
  // The construction std::pair<DS,DS>(a,b) appears as a sub-expression (not a
  // variable declaration, which would elaborate the type first), so it goes
  // through the constructor-call resolution that trips over the incomplete
  // std::pair<DS,DS> instance.
  __CPROVER_assert(
    std::pair<DS, DS>(a, b).first.no == 5,
    "pair<DS,DS> constructed with a member unordered_map present");
  __CPROVER_assert(std::pair<DS, DS>(a, b).first.no == 9, "WRONG must FAIL");
  return 0;
}
