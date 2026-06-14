// KNOWNBUG: std::string characters are not initialised on construction.
//
// libstdc++ ships std::__cxx11::basic_string<char> as an explicit
// instantiation declaration (`extern template class basic_string<char>;`).
// CBMC realises that class via the class_template_symbol /
// elaborate_class_template / parser-completion path, which — unlike
// instantiate_template — never runs the deferred-method-conversion loop
// for the instance's inline members.  As a result the character-copy
// helpers (basic_string<char>::_S_copy_chars -> _S_copy) stay in
// deferred_typechecking with an un-converted body and are then discarded
// (made nil) by cpp_typecheckt::clean_up(), turning the copy into a no-op.
//
// Consequently the LENGTH is stored correctly (size() == 2) but the
// CHARACTERS are left non-deterministic.  This is a soundness gap: the
// per-character assertions below are genuinely true at run time but CBMC
// reports them as FAILURE.
//
// Grounded in N5008 [temp.inst]/4 and [temp.inst] Note 4: an inline member
// that is the subject of an explicit instantiation *declaration* is not a
// declared specialization and must still be implicitly instantiated when
// odr-used.  When this is fixed, this test should verify SUCCESSFULLY and
// be reclassified from KNOWNBUG to CORE.

#include <string>

int main()
{
  std::string s = "ab";

  // The length is computed correctly today.
  __CPROVER_assert(s.size() == 2, "size() == 2");

  // The characters are NOT copied today (the bug): these are true at run
  // time but currently reported as FAILURE.
  __CPROVER_assert(s[0] == 'a', "s[0] == 'a'");
  __CPROVER_assert(s[1] == 'b', "s[1] == 'b'");

  return 0;
}
