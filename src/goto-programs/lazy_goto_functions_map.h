/// Author: Diffblue Ltd.

/// \file
/// A lazy wrapper for goto_functionst.

#ifndef CPROVER_GOTO_PROGRAMS_LAZY_GOTO_FUNCTIONS_MAP_H
#define CPROVER_GOTO_PROGRAMS_LAZY_GOTO_FUNCTIONS_MAP_H

#include <unordered_set>

#include "goto_functions.h"
#include "goto_convert_functions.h"

#include <langapi/language_file.h>
#include <util/journalling_symbol_table.h>
#include <util/message.h>
#include <util/symbol_table_builder.h>

/// Provides a wrapper for a map of lazily loaded goto_functiont.
/// This incrementally builds a goto-functions object, while permitting
/// access to goto programs while they are still under construction.
/// The intended workflow:
/// 1. The front-end registers the functions that are potentially
///   available, probably by use of langapi/language_file.h
/// 2. The main function registers functions that should be run on
///   each program, in sequence, after it is converted.
/// 3. Analyses will then access functions using the `at` function
/// \tparam bodyt: The type of the function bodies, usually goto_programt
class lazy_goto_functions_mapt final
{
public:
  // NOLINTNEXTLINE(readability/identifiers)  - name matches those used in STL
  typedef irep_idt key_type;
  // NOLINTNEXTLINE(readability/identifiers)  - name matches those used in STL
  typedef goto_functiont &mapped_type;
  /// The type of elements returned by const members
  // NOLINTNEXTLINE(readability/identifiers)  - name matches mapped_type
  typedef const goto_functiont &const_mapped_type;
  // NOLINTNEXTLINE(readability/identifiers)  - name matches those used in STL
  typedef std::pair<const key_type, goto_functiont> value_type;
  // NOLINTNEXTLINE(readability/identifiers)  - name matches those used in STL
  typedef value_type &reference;
  // NOLINTNEXTLINE(readability/identifiers)  - name matches those used in STL
  typedef const value_type &const_reference;
  // NOLINTNEXTLINE(readability/identifiers)  - name matches those used in STL
  typedef value_type *pointer;
  // NOLINTNEXTLINE(readability/identifiers)  - name matches those used in STL
  typedef const value_type *const_pointer;
  // NOLINTNEXTLINE(readability/identifiers)  - name matches those used in STL
  typedef std::size_t size_type;

  typedef
    std::function<void(
      const irep_idt &name,
      goto_functionst::goto_functiont &function,
      journalling_symbol_tablet &function_symbols)>
    post_process_functiont;
  typedef std::function<bool(const irep_idt &name)>
    can_generate_function_bodyt;
  typedef std::function<
    bool(
      const irep_idt &function_name,
      symbol_table_baset &symbol_table,
      goto_functiont &function,
      bool body_available)>
    generate_function_bodyt;

private:
  typedef std::map<key_type, goto_functiont> underlying_mapt;
  underlying_mapt &goto_functions;
  /// Names of functions that are already fully available in the programt state.
  /// \remarks These functions do not need processing before being returned
  /// whenever they are requested
  mutable std::unordered_set<irep_idt> processed_functions;

  language_filest &language_files;
  symbol_tablet &symbol_table;
  const post_process_functiont post_process_function;
  const can_generate_function_bodyt driver_program_can_generate_function_body;
  const generate_function_bodyt driver_program_generate_function_body;
  message_handlert &message_handler;

public:
  /// Creates a lazy_goto_functions_mapt.
  lazy_goto_functions_mapt(
    underlying_mapt &goto_functions,
    language_filest &language_files,
    symbol_tablet &symbol_table,
    post_process_functiont post_process_function,
    can_generate_function_bodyt driver_program_can_generate_function_body,
    generate_function_bodyt driver_program_generate_function_body,
    message_handlert &message_handler)
  : goto_functions(goto_functions),
    language_files(language_files),
    symbol_table(symbol_table),
    post_process_function(post_process_function),
    driver_program_can_generate_function_body(
      driver_program_can_generate_function_body),
    driver_program_generate_function_body(
      driver_program_generate_function_body),
    message_handler(message_handler)
  {
  }

  /// Gets the body for a given function.
  /// \param name: The name of the function to search for.
  /// \return The function body corresponding to the given function.
  const_mapped_type at(const key_type &name) const
  {
    return ensure_function_loaded_internal(name).second;
  }

  /// Gets the body for a given function.
  /// \param name: The name of the function to search for.
  /// \return The function body corresponding to the given function.
  mapped_type at(const key_type &name)
  {
    return ensure_function_loaded_internal(name).second;
  }

  /// Determines if this lazy GOTO functions map can produce a body for the
  /// given function
  /// \param name: function ID to query
  /// \return true if we can produce a function body, or false if we would leave
  ///   it a bodyless stub.
  bool can_produce_function(const key_type &name) const
  {
    return
      language_files.can_convert_lazy_method(name) ||
      driver_program_can_generate_function_body(name);
  }

  void unload(const key_type &name) const { goto_functions.erase(name); }

  void ensure_function_loaded(const key_type &name) const
  {
    ensure_function_loaded_internal(name);
  }

private:
  // This returns a non-const reference, but if you use this method from a
  // const method then you should not return such a reference without making it
  // const first
  reference ensure_function_loaded_internal(const key_type &name) const
  {
    symbol_table_buildert symbol_table_builder =
      symbol_table_buildert::wrap(symbol_table);

    journalling_symbol_tablet journalling_table =
      journalling_symbol_tablet::wrap(symbol_table_builder);
    reference named_function=ensure_entry_converted(name, journalling_table);
    mapped_type function=named_function.second;
    if(processed_functions.count(name)==0)
    {
      // Run function-pass conversions
      post_process_function(name, function, journalling_table);
      // Assign procedure-local location numbers for now
      function.body.compute_location_numbers();
      processed_functions.insert(name);
    }
    return named_function;
  }

  /// Convert a function if not already converted, then return a reference to
  /// its goto_functionst map entry.
  /// \param name: ID of the function to convert
  /// \param function_symbol_table: mutable symbol table reference to be used
  ///   when converting the function (e.g. to add new local variables).
  ///   Note we should not use a global pre-cached symbol table reference for
  ///   this so that our callers can insert a journalling table here if needed.
  /// \return reference to the new or existing goto_functions map entry.
  reference ensure_entry_converted(
    const key_type &name,
    symbol_table_baset &function_symbol_table) const
  {
    underlying_mapt::iterator it=goto_functions.find(name);
    if(it!=goto_functions.end())
      return *it;

    goto_functiont function;

    // First chance: see if the driver program wants to provide a replacement:
    bool body_provided =
      driver_program_generate_function_body(
        name,
        function_symbol_table,
        function,
        language_files.can_convert_lazy_method(name));

    // Second chance: see if language_filest can provide a body:
    if(!body_provided)
    {
      // Fill in symbol table entry body if not already done
      language_files.convert_lazy_method(name, function_symbol_table);
      body_provided = function_symbol_table.lookup_ref(name).value.is_not_nil();

      // Create goto_functiont
      goto_convert_functionst convert_functions(
        function_symbol_table, message_handler);
      convert_functions.convert_function(name, function);
    }

    // Add to map
    return *goto_functions.emplace(name, std::move(function)).first;
  }
};

#endif  // CPROVER_GOTO_PROGRAMS_LAZY_GOTO_FUNCTIONS_MAP_H
