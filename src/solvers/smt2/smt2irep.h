/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT2_SMT2IREP_H
#define CPROVER_SOLVERS_SMT2_SMT2IREP_H

#include <iosfwd>

#include <util/irep.h>
#include <util/optional.h>

class message_handlert;

/// returns an irep for an SMT-LIB2 expression read from a given stream
/// returns {} when EOF is encountered before reading non-whitespace input
optionalt<irept> smt2irep(std::istream &, message_handlert &);

#endif // CPROVER_SOLVERS_SMT2_SMT2IREP_H
