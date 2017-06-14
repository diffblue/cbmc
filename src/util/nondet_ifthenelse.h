/*******************************************************************\

Module: Nondeterministic if-then-else

Author: Chris Smowton, chris@smowton.net

\*******************************************************************/

/// \file
/// Nondeterministic if-then-else

#ifndef CPROVER_UTIL_NONDET_IFTHENELSE_H
#define CPROVER_UTIL_NONDET_IFTHENELSE_H

#include <util/std_code.h>

class symbol_tablet;
class source_locationt;

class nondet_ifthenelset
{
  code_blockt &result_code;
  symbol_tablet &symbol_table;
  const source_locationt &loc;
  irep_idt fresh_symbol_mode;
  code_labelt else_label;
  code_labelt join_label;
  const std::string choice_symname;
 public:
  nondet_ifthenelset(
    code_blockt &_result_code,
    symbol_tablet &_symbol_table,
    const source_locationt &_loc,
    const irep_idt &_fresh_symbol_mode,
    const std::string &name) :
    result_code(_result_code),
    symbol_table(_symbol_table),
    loc(_loc),
    fresh_symbol_mode(_fresh_symbol_mode),
    choice_symname(name)
    {}
  void begin_if();
  void begin_else();
  void finish();
};

#endif // CPROVER_UTIL_NONDET_IFTHENELSE_H
