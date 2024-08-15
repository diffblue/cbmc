/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT2_SMT2IREP_H
#define CPROVER_SOLVERS_SMT2_SMT2IREP_H

#include <iosfwd>
#include <optional>

class irept;
class message_handlert;

/// Returns an irep for an SMT-LIB2 expression read from a given stream
/// Returns {} when EOF is encountered before reading non-whitespace input
/// or on other parsing errors.
std::optional<irept> smt2irep(std::istream &, message_handlert &);

class smt2_tokenizert;

/// Returns an irep for an SMT-LIB2 expression read from a given tokenizer.
/// Returns {} when EOF is encountered before reading non-whitespace input.
/// Throws smt2_errort on parsing errors.
std::optional<irept> smt2irep(smt2_tokenizert &);

#endif // CPROVER_SOLVERS_SMT2_SMT2IREP_H
