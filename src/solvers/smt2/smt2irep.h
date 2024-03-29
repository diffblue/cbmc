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

/// returns an irep for an SMT-LIB2 expression read from a given stream
/// returns {} when EOF is encountered before reading non-whitespace input
std::optional<irept> smt2irep(std::istream &, message_handlert &);

#endif // CPROVER_SOLVERS_SMT2_SMT2IREP_H
