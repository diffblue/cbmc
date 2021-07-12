// Author: Diffblue Ltd.

/// \file
/// Streaming SMT data structures to a string based output stream.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_TO_STRING_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_TO_STRING_H

class smt_sortt;
class smt_termt;

#include <iosfwd>
#include <string>

std::ostream &operator<<(std::ostream &os, const smt_sortt &sort);
std::ostream &operator<<(std::ostream &os, const smt_termt &term);

std::string smt_to_string(const smt_sortt &sort);
std::string smt_to_string(const smt_termt &term);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_TO_STRING_H
