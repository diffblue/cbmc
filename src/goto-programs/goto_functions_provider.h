/*******************************************************************\

Module: Reduced wrapper interface to get goto functions

Author: Chris Smowton

Date: February 2018

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_PROVIDER_H
#define CPROVER_GOTO_PROGRAMS_GOTO_FUNCTIONS_PROVIDER_H

#include <unordered_set>

#include <goto-programs/goto_functions.h>
#include <goto-programs/lazy_goto_model.h>

/// GOTO functions reduced interface. Provides functions to get a GOTO function
/// by symbol id, and a function to get the set of existing functions (those for
/// which get_existing_goto_function will not throw).
/// This permits producing goto functions on demand, without having to support
/// the full interface of std::map that goto_functionst exposes across
/// operations with side-effects.
class goto_functions_providert
{
public:
  /// Get a GOTO function by name, or throw if no such function exists. This is
  /// guaranteed side-effect free.
  /// \param id: function to get
  /// \return function body
  virtual const goto_functionst::goto_functiont &get_existing_goto_function(
    const irep_idt &id) const = 0;

  /// Get a GOTO function by name, or throw if no such function exists.
  /// Unlike get_existing_goto_function, this may have side-effects on the
  /// symbol table, so symbol table iterators are not safe across calls.
  /// It may also add to the set returned by get_available_functions.
  /// \param id: function to get
  /// \return function body
  virtual const goto_functionst::goto_functiont &get_goto_function(
    const irep_idt &id) = 0;

  /// Get the set of available functions, for which get_existing_goto_function
  /// must not throw. get_goto_function may be able to supply functions not
  /// listed here, but if so it will have side-effects on the available
  /// functions set and symbol table, as their bodies are produced on demand.
  virtual std::unordered_set<irep_idt, irep_id_hash> get_available_functions()
    const = 0;
};

/// GOTO functions view backing onto a goto_functionst object. All functions are
/// available, in the sense that they can be accessed without side-effects.
class eager_goto_functions_providert : public goto_functions_providert
{
public:
  explicit eager_goto_functions_providert(
    const goto_functionst &goto_functions) :
    goto_functions(goto_functions)
  {
  }

  const goto_functionst::goto_functiont &get_existing_goto_function(
    const irep_idt &id) const override
  {
    return goto_functions.function_map.at(id);
  }

  const goto_functionst::goto_functiont &get_goto_function(
    const irep_idt &id) override
  {
    return get_existing_goto_function(id);
  }

  std::unordered_set<irep_idt, irep_id_hash> get_available_functions()
    const override
  {
    std::unordered_set<irep_idt, irep_id_hash> result;
    for(const auto &id_and_body : goto_functions.function_map)
      result.insert(id_and_body.first);
    return result;
  }

private:
  const goto_functionst &goto_functions;
};

/// GOTO functions provider backing onto a lazy goto model.
/// get_available_functions returns those that have already been converted,
/// either using get_goto_function or otherwise, and therefore can be accessed
/// again in a const context. get_goto_function may be able to convert other
/// functions on demand, but side-effects on the symbol table will result in
/// this case.
class lazy_goto_functions_providert : public goto_functions_providert
{
public:
  explicit lazy_goto_functions_providert(
    lazy_goto_modelt &lazy_goto_model) :
    lazy_goto_model(lazy_goto_model)
  {
  }

  const goto_functionst::goto_functiont &get_existing_goto_function(
    const irep_idt &id) const override
  {
    return lazy_goto_model.get_converted_goto_function(id);
  }

  const goto_functionst::goto_functiont &get_goto_function(
    const irep_idt &id) override
  {
    return lazy_goto_model.get_goto_function(id);
  }

  std::unordered_set<irep_idt, irep_id_hash> get_available_functions()
    const override
  {
    return lazy_goto_model.get_converted_functions();
  }

private:
  lazy_goto_modelt &lazy_goto_model;
};

#endif
