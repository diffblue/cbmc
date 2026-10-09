// goto-cc must correctly preprocess and compile a translation unit that
// constructs a std::optional<T> from a T value (the converting
// constructor optional(_Up&&)).
//
// goto-cc preprocesses each source to a .ii file with its own
// preprocessing pass and then feeds the already-preprocessed result to
// the front-end.  CBMC does not implement CTAD deduction guides
// ([over.match.class.deduct]); when cbmc preprocesses a .cpp directly it
// passes -U__cpp_deduction_guides so the guides are removed from library
// headers.  goto-cc's separate preprocessing pass used to omit that flag,
// so std::optional's deduction guide `optional(_Tp) -> optional<_Tp>`
// survived into the .ii and CBMC's parser mis-classified it as a
// constructor, aborting with "function must have return type" and then
// "invalid implicit conversion from 'T' to 'struct optional'".
//
// This made goto-cc and cbmc disagree on the same source.  The test
// keeps the optional construction in an uncalled function so the chained
// cbmc run stays tractable (no symbolic execution of std::optional's
// payload machinery); the point is that goto-cc *compiles* it without the
// spurious conversion error.

#include <optional>
#include <string>

std::optional<std::string> make_opt(const std::string &s)
{
  return s;
}

int main()
{
  return 0;
}
