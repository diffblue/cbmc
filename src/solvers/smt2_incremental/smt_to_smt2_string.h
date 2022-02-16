// Author: Diffblue Ltd.

/// \file
/// Streaming SMT data structures to a string based output stream. The generated
/// output strings are intended to be valid input for SMT2 solvers compliant
/// with the SMT-LIB standard version 2.6.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_TO_SMT2_STRING_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_TO_SMT2_STRING_H

class smt_indext;
class smt_sortt;
class smt_termt;
class smt_optiont;
class smt_commandt;
class smt_logict;

#include <iosfwd>
#include <string>

std::ostream &operator<<(std::ostream &os, const smt_indext &index);
std::ostream &operator<<(std::ostream &os, const smt_sortt &sort);
std::ostream &operator<<(std::ostream &os, const smt_termt &term);
std::ostream &operator<<(std::ostream &os, const smt_optiont &option);
std::ostream &operator<<(std::ostream &os, const smt_logict &logic);
std::ostream &operator<<(std::ostream &os, const smt_commandt &command);

std::string smt_to_smt2_string(const smt_indext &index);
std::string smt_to_smt2_string(const smt_sortt &sort);
std::string smt_to_smt2_string(const smt_termt &term);
std::string smt_to_smt2_string(const smt_optiont &option);
std::string smt_to_smt2_string(const smt_logict &logic);
std::string smt_to_smt2_string(const smt_commandt &command);

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_TO_SMT2_STRING_H
