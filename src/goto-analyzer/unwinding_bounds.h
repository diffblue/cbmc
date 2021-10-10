/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@city.ac.uk

\*******************************************************************/

#ifndef CPROVER_GOTO_ANALYZER_UNWINDING_BOUNDS_H
#define CPROVER_GOTO_ANALYZER_UNWINDING_BOUNDS_H

#include <iosfwd>

class ai_baset;
class goto_modelt;
class message_handlert;
class optionst;

/// Computes, where possible, upper bounds on the number of
/// unwinding iterations required to fully unwind a loop.
/// Depending on how the abstract domain is configured
/// this may find loop bounds that CBMC constant-propagation
/// unwinder doesn't find
bool unwinding_bounds(
  goto_modelt &,
  const ai_baset &,
  const optionst &,
  message_handlert &,
  std::ostream &);

#endif // CPROVER_GOTO_ANALYZER_UNWINDING_BOUNDS_H
