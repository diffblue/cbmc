/*******************************************************************\

Module: Symbol Table + CFG

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbol Table + CFG

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H

#include <util/journalling_symbol_table.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include "abstract_goto_model.h"
#include "goto_functions.h"
#include "validate_goto_model.h"

// A model is a pair consisting of a symbol table
// and the CFGs for the functions.

class goto_modelt : public abstract_goto_modelt
{
public:
  /// Symbol table. Direct access is deprecated; use the abstract_goto_modelt
  /// interface instead if possible.
  symbol_tablet symbol_table;
  /// GOTO functions. Direct access is deprecated; use the abstract_goto_modelt
  /// interface instead if possible.
  goto_functionst goto_functions;

  void clear()
  {
    symbol_table.clear();
    goto_functions.clear();
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

  /// Remove the function named \p name from the function map, if it exists.
  /// \return Returns 0 when \p name was not present, and 1 when \p name was
  ///   removed.
  std::size_t unload(const irep_idt &name)
  {
    return goto_functions.unload(name);
  }

  // Implement the abstract goto model interface:

  const goto_functionst &get_goto_functions() const override
  {
    return goto_functions;
  }

  const symbol_tablet &get_symbol_table() const override
  {
    return symbol_table;
  }

  const goto_functionst::goto_functiont &get_goto_function(
    const irep_idt &id) override
  {
    return goto_functions.function_map.at(id);
  }

  bool can_produce_function(const irep_idt &id) const override
  {
    return goto_functions.function_map.find(id) !=
           goto_functions.function_map.end();
  }

  /// Check that the goto model is well-formed
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  void validate(
    const validation_modet vm = validation_modet::INVARIANT,
    const goto_model_validation_optionst &goto_model_validation_options =
      goto_model_validation_optionst{}) const override
  {
    symbol_table.validate(vm);

    // Does a number of checks at the function_mapt level to ensure the
    // goto_program is well formed. Does not call any validate methods
    // (at the goto_functiont level or below)
    validate_goto_model(goto_functions, vm, goto_model_validation_options);

    const namespacet ns(symbol_table);
    goto_functions.validate(ns, vm);
  }
};

/// Class providing the abstract GOTO model interface onto an unrelated
/// symbol table and goto_functionst.
class wrapper_goto_modelt : public abstract_goto_modelt
{
public:
  wrapper_goto_modelt(
    const symbol_tablet &symbol_table,
    const goto_functionst &goto_functions) :
    symbol_table(symbol_table),
    goto_functions(goto_functions)
  {
  }

  const goto_functionst &get_goto_functions() const override
  {
    return goto_functions;
  }

  const symbol_tablet &get_symbol_table() const override
  {
    return symbol_table;
  }

  const goto_functionst::goto_functiont &get_goto_function(
    const irep_idt &id) override
  {
    return goto_functions.function_map.at(id);
  }

  bool can_produce_function(const irep_idt &id) const override
  {
    return goto_functions.function_map.find(id) !=
           goto_functions.function_map.end();
  }

  /// Check that the goto model is well-formed
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  void validate(
    const validation_modet vm,
    const goto_model_validation_optionst &goto_model_validation_options)
    const override
  {
    symbol_table.validate(vm);

    // Does a number of checks at the function_mapt level to ensure the
    // goto_program is well formed. Does not call any validate methods
    // (at the goto_functiont level or below)
    validate_goto_model(goto_functions, vm, goto_model_validation_options);

    const namespacet ns(symbol_table);
    goto_functions.validate(ns, vm);
  }

private:
  const symbol_tablet &symbol_table;
  const goto_functionst &goto_functions;
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
  /// \param symbol_table: Symbol table where any new symbols associated with
  ///   `goto_function` should be inserted
  /// \param goto_functions: `goto_functionst` that contains `goto_function`.
  ///   Only used to ensure unique numbering of `goto_function`, specifically
  ///   incrementing its `unused_location_number` member each time the program
  ///   is re-numbered.
  /// \param function_id: Name of function to wrap
  /// \param goto_function: Function to wrap
  goto_model_functiont(
    journalling_symbol_tablet &symbol_table,
    goto_functionst &goto_functions,
    const irep_idt &function_id,
    goto_functionst::goto_functiont &goto_function):
  symbol_table(symbol_table),
  goto_functions(goto_functions),
  function_id(function_id),
  goto_function(goto_function)
  {
  }

  /// Re-number our goto_function. After this method returns all instructions'
  /// location numbers may have changed, but will be globally unique and in
  /// program order within the program.
  void compute_location_numbers()
  {
    goto_functions.compute_location_numbers(goto_function.body);
  }

  /// Get symbol table
  /// \return journalling symbol table that (a) wraps the global symbol table,
  ///   and (b) has recorded all symbol mutations (insertions, updates and
  ///   deletions) that resulted from creating `goto_function`.
  journalling_symbol_tablet &get_symbol_table()
  {
    return symbol_table;
  }

  /// Get GOTO function
  /// \return the wrapped GOTO function
  goto_functionst::goto_functiont &get_goto_function()
  {
    return goto_function;
  }

  /// Get function id
  /// \return `goto_function`'s name (its key in `goto_functions`)
  const irep_idt &get_function_id()
  {
    return function_id;
  }

private:
  journalling_symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  irep_idt function_id;
  goto_functionst::goto_functiont &goto_function;
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_MODEL_H
