/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Dynamic frame condition checking library loading

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LIBRARY_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LIBRARY_H

#include <util/irep.h>
#include <util/message.h>
#include <util/optional.h>

#include <goto-programs/goto_instruction_code.h>

#include <map>
#include <set>

/// One enum value per type defined by the `cprover_dfcc.c` library file.
/// These enums are used to perform lookups into maps that contain the actual
/// symbols and to avoid using strings/irep_ids everywhere.
enum class dfcc_typet
{
  /// type of descriptors of conditionally assignable ranges of bytes
  CAR,
  /// type of sets of CAR
  CAR_SET,
  /// type of pointers to sets of CAR
  CAR_SET_PTR,
  /// type of sets of object identifiers
  OBJ_SET,
  /// type of pointers to sets of object identifiers
  OBJ_SET_PTR,
  /// type of descriptors of assignable/freeable sets of locations
  WRITE_SET,
  /// type of pointers to descriptors of assignable/freeable sets of locations
  WRITE_SET_PTR
};

/// One enum value per function defined by the `cprover_dfcc.c` library file.
/// These enums are used to perform lookups into maps that contain the actual
/// symbols and to avoid using strings/irep_ids everywhere.
enum class dfcc_funt
{
  /// \see __CPROVER_contracts_car_create
  CAR_CREATE,
  /// \see __CPROVER_contracts_car_set_create
  CAR_SET_CREATE,
  /// \see __CPROVER_contracts_car_set_insert
  CAR_SET_INSERT,
  /// \see __CPROVER_contracts_car_set_remove
  CAR_SET_REMOVE,
  /// \see __CPROVER_contracts_car_set_contains
  CAR_SET_CONTAINS,
  /// \see __CPROVER_contracts_obj_set_create_indexed_by_object_id
  OBJ_SET_CREATE_INDEXED_BY_OBJECT_ID,
  /// \see __CPROVER_contracts_obj_set_create_append
  OBJ_SET_CREATE_APPEND,
  /// \see __CPROVER_contracts_obj_set_release
  OBJ_SET_RELEASE,
  /// \see __CPROVER_contracts_obj_set_add
  OBJ_SET_ADD,
  /// \see __CPROVER_contracts_obj_set_append
  OBJ_SET_APPEND,
  /// \see __CPROVER_contracts_obj_set_remove
  OBJ_SET_REMOVE,
  /// \see __CPROVER_contracts_obj_set_contains
  OBJ_SET_CONTAINS,
  /// \see __CPROVER_contracts_obj_set_contains_exact
  OBJ_SET_CONTAINS_EXACT,
  /// \see __CPROVER_contracts_write_set_create
  WRITE_SET_CREATE,
  /// \see __CPROVER_contracts_write_set_release
  WRITE_SET_RELEASE,
  /// \see __CPROVER_contracts_write_set_insert_assignable
  WRITE_SET_INSERT_ASSIGNABLE,
  /// \see __CPROVER_contracts_write_set_insert_object_whole
  WRITE_SET_INSERT_OBJECT_WHOLE,
  /// \see __CPROVER_contracts_write_set_insert_object_from
  WRITE_SET_INSERT_OBJECT_FROM,
  /// \see __CPROVER_contracts_write_set_object_upto
  WRITE_SET_INSERT_OBJECT_UPTO,
  /// \see __CPROVER_contracts_write_set_add_freeable
  WRITE_SET_ADD_FREEABLE,
  /// \see __CPROVER_contracts_write_set_add_allocated
  WRITE_SET_ADD_ALLOCATED,
  /// \see __CPROVER_contracts_write_set_add_decl
  WRITE_SET_ADD_DECL,
  /// \see __CPROVER_contracts_write_set_record_dead
  WRITE_SET_RECORD_DEAD,
  /// \see __CPROVER_contracts_write_set_record_deallocated
  WRITE_SET_RECORD_DEALLOCATED,
  /// \see __CPROVER_contracts_write_set_check_allocated_deallocated_is_empty
  WRITE_SET_CHECK_ALLOCATED_DEALLOCATED_IS_EMPTY,
  /// \see __CPROVER_contracts_write_set_check_assignment
  WRITE_SET_CHECK_ASSIGNMENT,
  /// \see __CPROVER_contracts_write_set_check_array_set
  WRITE_SET_CHECK_ARRAY_SET,
  /// \see __CPROVER_contracts_write_set_check_array_copy
  WRITE_SET_CHECK_ARRAY_COPY,
  /// \see __CPROVER_contracts_write_set_check_array_replace
  WRITE_SET_CHECK_ARRAY_REPLACE,
  /// \see __CPROVER_contracts_write_set_check_havoc_object
  WRITE_SET_CHECK_HAVOC_OBJECT,
  /// \see __CPROVER_contracts_write_set_check_deallocate
  WRITE_SET_CHECK_DEALLOCATE,
  /// \see __CPROVER_contracts_write_set_check_assigns_clause_inclusion
  WRITE_SET_CHECK_ASSIGNS_CLAUSE_INCLUSION,
  /// \see __CPROVER_contracts_write_set_check_frees_clause_inclusion
  WRITE_SET_CHECK_FREES_CLAUSE_INCLUSION,
  /// \see __CPROVER_contracts_write_set_deallocate_freeable
  WRITE_SET_DEALLOCATE_FREEABLE,
  /// \see __CPROVER_contracts_write_set_havoc_get_assignable_target
  WRITE_SET_HAVOC_GET_ASSIGNABLE_TARGET,
  /// \see __CPROVER_contracts_write_set_havoc_object_whole
  WRITE_SET_HAVOC_OBJECT_WHOLE,
  /// \see __CPROVER_contracts_write_set_havoc_slice
  WRITE_SET_HAVOC_SLICE,
  /// \see __CPROVER_contracts_link_is_fresh
  LINK_IS_FRESH,
  /// \see __CPROVER_contracts_link_allocated
  LINK_ALLOCATED,
  /// \see __CPROVER_contracts_link_deallocated
  LINK_DEALLOCATED,
  /// \see __CPROVER_contracts_is_fresh
  IS_FRESH,
  /// \see __CPROVER_contracts_pointer_in_range_dfcc
  POINTER_IN_RANGE_DFCC,
  /// \see __CPROVER_contracts_is_freeable
  IS_FREEABLE,
  /// \see __CPROVER_contracts_was_freed
  WAS_FREED,
  /// \see __CPROVER_contracts_check_replace_ensures_was_freed_preconditions
  REPLACE_ENSURES_WAS_FREED_PRECONDITIONS,
  /// \see __CPROVER_contracts_obeys_contract
  OBEYS_CONTRACT,
};

class goto_modelt;
class goto_functiont;
class goto_programt;
class message_handlert;
class symbolt;
class symbol_exprt;
class typet;
class dfcc_utilst;

/// Class interface to library types and functions defined in
/// `cprover_contracts.c`.
class dfcc_libraryt
{
public:
  dfcc_libraryt(
    goto_modelt &goto_model,
    dfcc_utilst &utils,
    message_handlert &lmessage_handler);

protected:
  /// True iff the contracts library symbols are loaded
  static bool loaded;

  /// True iff the library functions are inlined
  static bool inlined;

  /// True iff the library functions are specialized
  /// to a particular contract
  static bool specialized;

  /// True iff the library functions uses of malloc and free are fixed
  static bool malloc_free_fixed;

  goto_modelt &goto_model;
  dfcc_utilst &utils;
  message_handlert &message_handler;
  messaget log;

  /// Collects the names of all library functions currently missing from the
  /// goto_model into `missing`.
  std::set<irep_idt> get_missing_funs();

  /// Inlines library functions that need to be inlined before use
  void inline_functions();

  /// Fixes function calls to malloc and free in library functions.
  /// Change calls to `__CPROVER_contracts_malloc` into calls to `malloc`
  /// Change calls to `__CPROVER_contracts_free` into calls to `free`
  void fix_malloc_free_calls();

private:
  /// Enum to type name mapping
  const std::map<dfcc_typet, irep_idt> dfcc_type_to_name;

  /// Swapped dfcc_type_to_name
  const std::map<irep_idt, dfcc_typet> dfcc_name_to_type;

  /// enum to function name mapping
  const std::map<dfcc_funt, irep_idt> dfcc_fun_to_name;

  // Swapped dfcc_fun_to_name
  const std::map<irep_idt, dfcc_funt> dfcc_name_to_fun;

  /// Maps built-in function names to enums to use for instrumentation
  const std::map<irep_idt, dfcc_funt> dfcc_hook;

  /// Maps front-end functions to library functions giving their havoc semantics
  const std::map<irep_idt, dfcc_funt> havoc_hook;

  /// All built-in function names (front-end and instrumentation hooks)
  const std::set<irep_idt> assignable_builtin_names;

public:
  /// Maps enum values to the actual types (dynamically loaded)
  std::map<dfcc_typet, typet> dfcc_type;

  /// Maps enum values to the actual function symbols (dynamically loaded)
  std::map<dfcc_funt, symbolt> dfcc_fun_symbol;

  /// After calling this function, all library types and functions are present
  /// in the the goto_model. Any other functions that the DFCC functions rely on
  /// and need to be instrumented will be added to `to_instrument`
  void load(std::set<irep_idt> &to_instrument);

  /// Returns the dfcc_funt that corresponds to the given id if any.
  optionalt<dfcc_funt> get_dfcc_fun(const irep_idt &id) const;

  /// Returns the name of the given dfcc_funt.
  const irep_idt &get_dfcc_fun_name(dfcc_funt fun) const;

  /// True iff the given id is one of the library symbols.
  bool is_dfcc_library_symbol(const irep_idt &id) const;

  /// Specializes the library by unwinding loops in library functions
  /// to the given assigns clause size.
  /// \param contract_assigns_size_hint size of the assigns clause being checked
  void specialize(const std::size_t contract_assigns_size_hint);

  /// Adds an ASSERT(false) body to all front-end functions
  /// __CPROVER_object_whole
  /// __CPROVER_object_upto
  /// __CPROVER_object_from
  /// __CPROVER_assignable
  /// __CPROVER_freeable
  /// An error will be triggered in case calls to these functions occur outside
  /// of a contrat clause and were hence not mapped to their library
  /// implementation.
  void inhibit_front_end_builtins();

  /// Adds "checked" pragmas to instructions of all library functions
  /// instructions. By default checks are not disabled.
  void disable_checks();

  /// Returns true iff the given function_id is one of `__CPROVER_assignable`,
  /// `__CPROVER_object_whole`, `__CPROVER_object_from`,
  /// `__CPROVER_object_upto`, `__CPROVER_freeable`
  bool is_front_end_builtin(const irep_idt &function_id) const;

  /// Returns the library instrumentation hook for the given front-end function.
  /// \pre  \p function_id is a front end built-in as defined by
  /// \ref is_front_end_builtin.
  dfcc_funt get_hook(const irep_idt &function_id) const;

  /// Returns the library instrumentation hook for the given built-in.
  /// function_id must be one of `__CPROVER_assignable`,
  /// `__CPROVER_object_whole`, `__CPROVER_object_from`, `__CPROVER_object_upto`
  optionalt<dfcc_funt> get_havoc_hook(const irep_idt &function_id) const;

  /// \brief Returns the "__dfcc_instrumented_functions" symbol or creates it if
  /// it does not exist already.
  /// This symbol is an unbounded map of booleans indexed
  /// by function pointer ID, meant to have value true for instrumented
  /// functions and false for non-instrumented functions.
  /// Initialisation instructions for this map are generated by
  /// \ref add_instrumented_functions_map_init_instructions
  const symbolt &get_instrumented_functions_map_symbol();

  /// Generates instructions to initialize the instrumented function map
  /// symbol from the given set of instrumented function
  void add_instrumented_functions_map_init_instructions(
    const std::set<irep_idt> &instrumented_functions,
    const source_locationt &source_location,
    goto_programt &dest);

  /// \brief Builds call to \ref __CPROVER_contracts_write_set_create
  const code_function_callt write_set_create_call(
    const exprt &write_set_ptr,
    const exprt &contract_assigns_size,
    const exprt &contract_frees_size,
    const exprt &assume_requires_ctx,
    const exprt &assert_requires_ctx,
    const exprt &assume_ensures_ctx,
    const exprt &assert_ensures_ctx,
    const exprt &allow_allocate,
    const exprt &allow_deallocate,
    const source_locationt &source_location);

  /// \brief Builds call to \ref __CPROVER_contracts_write_set_release
  const code_function_callt write_set_release_call(
    const exprt &write_set_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to \ref __CPROVER_contracts_write_set_add_allocated
  const code_function_callt write_set_add_allocated_call(
    const exprt &write_set_ptr,
    const exprt &ptr,
    const source_locationt &source_location);

  /// \brief Builds call to \ref __CPROVER_contracts_write_set_add_decl
  const code_function_callt write_set_add_decl_call(
    const exprt &write_set_ptr,
    const exprt &ptr,
    const source_locationt &source_location);

  /// \brief Builds call to \ref __CPROVER_contracts_write_set_record_dead
  const code_function_callt write_set_record_dead_call(
    const exprt &write_set_ptr,
    const exprt &ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_record_deallocated
  const code_function_callt write_set_record_deallocated_call(
    const exprt &write_set_ptr,
    const exprt &ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_check_allocated_deallocated_is_empty
  const code_function_callt write_set_check_allocated_deallocated_is_empty_call(
    const exprt &check_var,
    const exprt &write_set_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_check_assignment
  const code_function_callt write_set_check_assignment_call(
    const exprt &check_var,
    const exprt &write_set_ptr,
    const exprt &ptr,
    const exprt &size,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_check_array_set
  const code_function_callt write_set_check_array_set_call(
    const exprt &check_var,
    const exprt &write_set_ptr,
    const exprt &dest,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_check_array_copy
  const code_function_callt write_set_check_array_copy_call(
    const exprt &check_var,
    const exprt &write_set_ptr,
    const exprt &dest,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_check_array_replace
  const code_function_callt write_set_check_array_replace_call(
    const exprt &check_var,
    const exprt &write_set_ptr,
    const exprt &dest,
    const exprt &src,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_check_havoc_object
  const code_function_callt write_set_check_havoc_object_call(
    const exprt &check_var,
    const exprt &write_set_ptr,
    const exprt &ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_check_deallocate
  const code_function_callt write_set_check_deallocate_call(
    const exprt &check_var,
    const exprt &write_set_ptr,
    const exprt &ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_check_assigns_clause_inclusion
  const code_function_callt write_set_check_assigns_clause_inclusion_call(
    const exprt &check_var,
    const exprt &reference_write_set_ptr,
    const exprt &candidate_write_set_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_check_frees_clause_inclusion
  const code_function_callt write_set_check_frees_clause_inclusion_call(
    const exprt &check_var,
    const exprt &reference_write_set_ptr,
    const exprt &candidate_write_set_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_write_set_deallocate_freeable
  const code_function_callt write_set_deallocate_freeable_call(
    const exprt &write_set_ptr,
    const exprt &target_write_set_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_link_is_fresh
  const code_function_callt link_is_fresh_call(
    const exprt &write_set_ptr,
    const exprt &is_fresh_obj_set_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_link_allocated
  const code_function_callt link_allocated_call(
    const exprt &write_set_postconditions_ptr,
    const exprt &write_set_to_link_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_link_deallocated
  const code_function_callt link_deallocated_call(
    const exprt &write_set_postconditions_ptr,
    const exprt &write_set_to_link_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_check_replace_ensures_was_freed_preconditions
  const code_function_callt check_replace_ensures_was_freed_preconditions_call(
    const exprt &ptr,
    const exprt &write_set_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_obj_set_create_indexed_by_object_id
  const code_function_callt obj_set_create_indexed_by_object_id_call(
    const exprt &obj_set_ptr,
    const source_locationt &source_location);

  /// \brief Builds call to
  /// \ref __CPROVER_contracts_obj_set_release
  const code_function_callt obj_set_release_call(
    const exprt &obj_set_ptr,
    const source_locationt &source_location);
};

#endif
