/*******************************************************************\

Module: Invariant helper utilities

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_INVARIANT_TYPES_H
#define CPROVER_UTIL_INVARIANT_TYPES_H

#include "invariant.h"

#include <string>

class irept;

/// Produces a plain string error description from an irep and some
/// explanatory text. If `problem_node` is nil, returns `description`.
/// \param problem_node: irep to pretty-print
/// \param description: descriptive text to prepend
/// \return error message
std::string pretty_print_invariant_with_irep(
  const irept &problem_node,
  const std::string &description);

/// Equivalent to
/// `INVARIANT_STRUCTURED(CONDITION, invariant_failedt,
///   pretty_print_invariant_with_irep(IREP, DESCRIPTION))`
#define INVARIANT_WITH_IREP(CONDITION, DESCRIPTION, IREP)               \
  INVARIANT_STRUCTURED(                                                 \
    CONDITION,                                                          \
    invariant_failedt,                                                  \
    pretty_print_invariant_with_irep((IREP), (DESCRIPTION)))

/// See `INVARIANT_WITH_IREP`
#define PRECONDITION_WITH_IREP(CONDITION, DESCRIPTION, IREP) \
  INVARIANT_WITH_IREP((CONDITION), (DESCRIPTION), (IREP))
#define POSTCONDITION_WITH_IREP(CONDITION, DESCRIPTION, IREP) \
  INVARIANT_WITH_IREP((CONDITION), (DESCRIPTION), (IREP))
#define CHECK_RETURN_WITH_IREP(CONDITION, DESCRIPTION, IREP) \
  INVARIANT_WITH_IREP((CONDITION), (DESCRIPTION), (IREP))
#define UNREACHABLE_WITH_IREP(CONDITION, DESCRIPTION, IREP) \
  INVARIANT_WITH_IREP((CONDITION), (DESCRIPTION), (IREP))
#define DATA_INVARIANT_WITH_IREP(CONDITION, DESCRIPTION, IREP) \
  INVARIANT_WITH_IREP((CONDITION), (DESCRIPTION), (IREP))

#endif
