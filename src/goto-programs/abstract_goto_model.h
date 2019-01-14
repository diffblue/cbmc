/*******************************************************************\

Module: Abstract GOTO Model

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Abstract interface to eager or lazy GOTO models

#ifndef CPROVER_GOTO_PROGRAMS_ABSTRACT_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_ABSTRACT_GOTO_MODEL_H

#include "goto_functions.h"
#include <util/symbol_table.h>

/// Abstract interface to eager or lazy GOTO models
class abstract_goto_modelt
{
public:
  virtual ~abstract_goto_modelt()
  {
  }

  /// Determines if this model can produce a body for the given function
  /// \param id: function ID to query
  /// \return true if we can produce a function body, or false if we would leave
  ///   it a bodyless stub.
  virtual bool can_produce_function(const irep_idt &id) const = 0;

  /// Get a GOTO function by name, or throw if no such function exists.
  /// May have side-effects on the GOTO function map provided by
  /// get_goto_functions, or the symbol table returned by get_symbol_table,
  /// so iterators pointing into either may be invalidated.
  /// \param id: function to get
  /// \return goto function
  virtual const goto_functionst::goto_functiont &get_goto_function(
    const irep_idt &id) = 0;

  /// Accessor to get a raw goto_functionst. Concurrent use of get_goto_function
  /// may invalidate iterators or otherwise surprise users by modifying the map
  /// underneath them, so this should only be used to lend a reference to code
  /// that cannot also call get_goto_function.
  virtual const goto_functionst &get_goto_functions() const = 0;

  /// Accessor to get the symbol table. Concurrent use of get_goto_function
  /// may invalidate iterators or otherwise surprise users by modifying the map
  /// underneath them, so this should only be used to lend a reference to code
  /// that cannot also call get_goto_function.
  virtual const symbol_tablet &get_symbol_table() const = 0;

  /// Check that the goto model is well-formed
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  virtual void validate(const validation_modet vm) const = 0;
};

#endif
