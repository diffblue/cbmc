/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_ANSI_C_C_PREPROCESS_H
#define CPROVER_ANSI_C_C_PREPROCESS_H

#include <iosfwd>
#include <string>
#include <vector>

class message_handlert;

bool c_preprocess(
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler);

bool c_preprocess(
  std::istream &instream,
  std::ostream &outstream,
  message_handlert &message_handler);

/// CBMC-specific C++ preprocessor feature-macro flags for the C++
/// standard currently selected in `config.cpp.cpp_standard`.
///
/// CBMC does not implement some standard-library features (CTAD
/// deduction guides per [over.match.class.deduct], `char8_t`, Parallel
/// STL); these `-U`/`-D` flags keep standard-library headers consistent
/// with CBMC's parser/typechecker.  Shared between `c_preprocess` (the
/// direct `.cpp` path used by cbmc) and goto-cc's own preprocessing
/// pass, so both produce identical preprocessed translation units.
std::vector<std::string> cprover_cxx_preprocessor_macro_flags();

// returns 'true' in case of error
bool test_c_preprocessor(message_handlert &message_handler);

#endif // CPROVER_ANSI_C_C_PREPROCESS_H
