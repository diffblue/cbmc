// Regression test: std::string characters are initialised on construction.
//
// libstdc++ ships std::__cxx11::basic_string<char> as an explicit
// instantiation declaration (`extern template class basic_string<char>;`).
// CBMC realises that class via the incomplete-to-complete swap in
// typecheck_compound_type rather than via instantiate_template, so its
// inline character-copy helpers (basic_string<char>::_S_copy_chars ->
// _S_copy) used to keep an un-converted body that was then discarded by
// cpp_typecheckt::clean_up(), turning the copy into a no-op: the LENGTH was
// stored correctly but the CHARACTERS were left non-deterministic.
//
// queue_deferred_methods_of_instance() now instantiates those inline member
// bodies at the instance-completion site, so the per-character assertions
// below hold.  Grounded in N5008 [temp.inst]/4 and Note 4 (an inline member
// that is the subject of an explicit instantiation declaration must still be
// implicitly instantiated when odr-used).  See
// doc/architectural/cpp-extern-template-member-instantiation.md.

#include <string>

int main()
{
  std::string s = "ab";

  __CPROVER_assert(s.size() == 2, "size() == 2");
  __CPROVER_assert(s[0] == 'a', "s[0] == 'a'");
  __CPROVER_assert(s[1] == 'b', "s[1] == 'b'");

  return 0;
}
