/*******************************************************************\

Module: Symbol Table + CFG

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbol Table + CFG

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H

#include <util/symbol_table.h>

#include "goto_functions.h"

// A model is a pair consisting of a symbol table
// and the CFGs for the functions.

class goto_modelt
{
public:
  symbol_tablet symbol_table;
  goto_functionst goto_functions;

  void clear()
  {
    symbol_table.clear();
    goto_functions.clear();
  }

  void output(std::ostream &out) const
  {
    namespacet ns(symbol_table);
    goto_functions.output(ns, out);
  }

  goto_modelt()
  {
  }

  // Copying is normally too expensive
  goto_modelt(const goto_modelt &)=delete;
  goto_modelt &operator=(const goto_modelt &)=delete;

  // Move operations need to be explicitly enabled as they are deleted with the
  // copy operations
  // default for move operations isn't available on Windows yet, so define
  //  explicitly (see https://msdn.microsoft.com/en-us/library/hh567368.aspx
  //  under "Defaulted and Deleted Functions")

  goto_modelt(goto_modelt &&other):
    symbol_table(std::move(other.symbol_table)),
    goto_functions(std::move(other.goto_functions))
  {
  }

  goto_modelt &operator=(goto_modelt &&other)
  {
    symbol_table=std::move(other.symbol_table);
    goto_functions=std::move(other.goto_functions);
    return *this;
  }

  void unload(const irep_idt &name) { goto_functions.unload(name); }
};

/// Interface providing access to a single function in a GOTO model, plus its
/// associated symbol table.
/// Its purpose is to permit GOTO program renumbering (a non-const operation on
/// goto_functionst) without providing a non-const reference to the entire
/// function map. For example, incremental function loading uses this, as in
/// that situation functions other than the one currently being loaded should
/// not be altered.
class goto_model_functiont
{
public:
  /// Construct a function wrapper
  /// \param goto_model: will be used to ensure unique numbering of
  ///   goto programs, specifically incrementing its unused_location_number
  ///   member each time a program is re-numbered.
  /// \param goto_function: function to wrap.
  explicit goto_model_functiont(
    goto_modelt &goto_model, goto_functionst::goto_functiont &goto_function):
  goto_model(goto_model),
  goto_function(goto_function)
  {
  }

  /// Re-number our goto_function. After this method returns all instructions'
  /// location numbers may have changed, but will be globally unique and in
  /// program order within the program.
  void compute_location_numbers()
  {
    goto_model.goto_functions.compute_location_numbers(goto_function.body);
  }

  /// Get symbol table
  /// \return symbol table from the associated GOTO model
  symbol_tablet &get_symbol_table()
  {
    return goto_model.symbol_table;
  }

  /// Get GOTO function
  /// \return the wrapped GOTO function
  goto_functionst::goto_functiont &get_goto_function()
  {
    return goto_function;
  }

  /// Get GOTO model. This returns a const reference because this interface is
  /// intended for use where non-const access to the whole model should not be
  /// allowed.
  /// \return const view of the whole GOTO model.
  const goto_modelt &get_goto_model()
  {
    return goto_model;
  }

private:
  goto_modelt &goto_model;
  goto_functionst::goto_functiont &goto_function;
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H
