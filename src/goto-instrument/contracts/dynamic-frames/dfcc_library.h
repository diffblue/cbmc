/*******************************************************************\

Module: Dynamic frame condition checking for function contracts

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Dynamic frame condition checking library loading

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LIBRARY_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_DYNAMIC_FRAMES_DFCC_LIBRARY_H

#include <util/irep.h>
#include <util/optional.h>

#include <map>
#include <set>

/// One enum value per type defined by the `cprover_dfcc.c` library file.
/// These enums are used to perform lookups into maps that contain the actual
/// symbols and to avoid using strings/irep_ids everywhere.
enum class dfcc_typet
{
  /// return type of functions that specify freeable locations (declarative)
  FREEABLE,
  /// return type of functions that specify assignable locations (declarative)
  ASSIGNABLE,
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
  /// Creates and returns a CAR from a pointer and a size
  CAR_CREATE,
  /// Create a CAR_SET that can to hold up to N elements
  CAR_SET_CREATE,
  /// Inserts a CAR in the CAR_SET at a given index
  CAR_SET_INSERT,
  /// Removes all CAR that contain the given pointer from the CAR_SET
  CAR_SET_REMOVE,
  /// Returns true iff the candidate CAR is contained in one of the set's CAR
  CAR_SET_CONTAINS,
  /// Create an OBJ_SET where pointers are keyed under their object ID
  OBJ_SET_CREATE_INDEXED_BY_OBJECT_ID,
  /// Create an OBJ_SET where pointers are appended at the end
  OBJ_SET_CREATE_APPEND,
  /// Adds a pointer's object to the OBJ_SET (by object ID)
  OBJ_SET_ADD,
  /// Adds a pointer's object to the OBJ_SET (by rank)
  OBJ_SET_APPEND,
  /// Removes a pointer's object to the OBJ_SET (by rank)
  OBJ_SET_REMOVE,
  /// True iff the CAR_SET contains a given pointer's object ID
  OBJ_SET_CONTAINS,
  /// True iff the CAR_SET contains a given pointer (exactly that pointer)
  OBJ_SET_CONTAINS_EXACT,
  /// Initialises a given WRITE_SET object
  WRITE_SET_CREATE,
  /// Releases dynamic objects representing an WRITE_SET
  WRITE_SET_RELEASE,
  /// Inserts an `CPROVER_PREFIX assignable` location in the WRITE_SET
  WRITE_SET_INSERT_ASSIGNABLE,
  /// Inserts a `CPROVER_PREFIX whole_object` location in the WRITE_SET
  WRITE_SET_INSERT_WHOLE_OBJECT,
  /// Inserts an `CPROVER_PREFIX object_from` location in the WRITE_SET
  WRITE_SET_INSERT_OBJECT_FROM,
  /// Inserts an `CPROVER_PREFIX upto` location in the WRITE_SET
  WRITE_SET_INSERT_OBJECT_UPTO,
  /// Inserts an `CPROVER_PREFIX freeable` location in the WRITE_SET
  WRITE_SET_ADD_FREEABLE,
  /// Inserts an locally `DECL` or heap-allocated object in the WRITE_SET
  WRITE_SET_ADD_ALLOCATED,
  /// Records a DEAD object from the WRITE_SET
  WRITE_SET_RECORD_DEAD,
  /// Records a deallocated object from the WRITE_SET
  WRITE_SET_RECORD_DEALLOCATED,
  /// True iff `set->allocated` and `set->deallocated` are empty
  WRITE_SET_CHECK_ALLOCATED_DEALLOCATED_IS_EMPTY,
  /// Checks if an assignment to a range (ptr, size) is allowed by the WRITE_SET
  WRITE_SET_CHECK_ASSIGNMENT,
  /// Checks if a `CALL array_set(dest, value)` is allowed by the WRITE_SET
  WRITE_SET_CHECK_ARRAY_SET,
  /// Checks if a `CALL array_copy(dest, src)` is allowed by the WRITE_SET
  WRITE_SET_CHECK_ARRAY_COPY,
  /// Checks if a `CALL array_replace(dest, src)` is allowed by the WRITE_SET
  WRITE_SET_CHECK_ARRAY_REPLACE,
  /// Checks if a `CALL havoc_object(ptr)` is allowed by the WRITE_SET
  WRITE_SET_CHECK_HAVOC_OBJECT,
  /// Checks if a `CALL deallocate(ptr)` is allowed by the WRITE_SET
  WRITE_SET_CHECK_DEALLOCATE,
  /// Checks if `candidate->contract_assigns` is contained in `reference`
  WRITE_SET_CHECK_ASSIGNS_CLAUSE_INCLUSION,
  /// Checks if `candidate->contract_frees` is contained in `reference`
  WRITE_SET_CHECK_FREES_CLAUSE_INCLUSION,
  /// Deallocates nondeterministically `set->contract_frees`
  WRITE_SET_DEALLOCATE_FREEABLE,
  /// Returns the start address of a CAR at some given rank in the WRITE_SET
  WRITE_SET_HAVOC_GET_ASSIGNABLE_TARGET,
  /// call `havoc_object(car.lb)` at some given rank in the WRITE_SET
  WRITE_SET_HAVOC_WHOLE_OBJECT,
  /// call `havoc_slice(CAR.lb, CAR.size)` at given rank in the WRITE_SET
  WRITE_SET_HAVOC_OBJECT_FROM,
  /// call `havoc_slice(CAR.lb, CAR.size)` at given rank in the WRITE_SET
  WRITE_SET_HAVOC_OBJECT_UPTO,
  /// Links a caller's WRITE_SET to a contract replacement WRITE_SET
  /// so that allocations performed by is_freshr in postconditions get recorded
  /// in the caller's WRITE_SET.
  LINK_IS_FRESHR_ALLOCATED,
  /// Makes a WRITE_SET linked_deallocated pointer point to the deallocated set
  /// of a second write set.
  LINK_DEALLOCATED,
  /// Implementation of is_fresh/is_freshr
  IS_FRESHR,
  /// Returns true iff a pointer satisfies the preconditions of `free`
  IS_FREEABLE,
  /// Returns true iff a pointer was recorded as deallocted
  /// in the given WRITE_SET
  IS_FREED,
  /// Extra preconditions checked by IS_FREED in assumption contexts,
  /// to detect vacuity caused by ASSUME(is_freed(ptr));
  REPLACE_ENSURES_IS_FREED_PRECONDITIONS
};

class goto_modelt;
class goto_functiont;
class goto_programt;
class messaget;
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
  dfcc_libraryt(goto_modelt &goto_model, dfcc_utilst &utils, messaget &log);

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
  messaget &log;
  message_handlert &message_handler;

  /// Collects the names of all library functions currently missing from the
  /// goto_model into `missing`. The ones that also need to be instrumented
  /// are added to `to_instrument`.
  void get_missing_funs(
    std::set<irep_idt> &missing,
    std::set<irep_idt> &to_instrument);

  /// Inlines library functions that need to be inlined before use
  void inline_functions();

  /// Fixes function calls to malloc and free in library functions.
  /// Change calls to `__CPROVER_contracts_malloc` into calls to `malloc`
  /// Change calls to `__CPROVER_contracts_free` into calls to `free`
  void fix_malloc_free_calls();

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
  void specialize(const int contract_assigns_size_hint);

  /// Adds an ASSERT(false) body to all front-end functions
  /// __CPROVER_whole_object
  /// __CPROVER_object_upto
  /// __CPROVER_object_from
  /// __CPROVER_assignable
  /// __CPROVER_freeable
  /// To make sure they cannot be used in a proof unexpectedly
  /// without causing verification errors.
  void inhibit_front_end_builtins();

  /// Sets the given hide flag on all instructions of all library functions
  void set_hide(bool hide);

  /// Returns the library instrumentation hook for the given built-in.
  /// function_id must be one of `__CPROVER_assignable`,
  /// `__CPROVER_whole_object`, `__CPROVER_object_from`,
  /// `__CPROVER_object_upto`, `__CPROVER_freeable`
  optionalt<dfcc_funt> get_hook(const irep_idt &function_id) const;

  /// Returns the library instrumentation hook for the given built-in.
  /// function_id must be one of `__CPROVER_assignable`,
  /// `__CPROVER_whole_object`, `__CPROVER_object_from`, `__CPROVER_object_upto`
  optionalt<dfcc_funt> get_havoc_hook(const irep_idt &function_id) const;

  /// Returns the "__dfcc_instrumented_functions" symbol or creates it if it
  /// does not exist already.
  /// This symbol is an unbounded map of booleans indexed
  /// by function pointer ID, that holds value true for functions
  /// that accept an extra write set parameter and false ones that don't.
  /// To have this map actually defined one must call
  /// \ref create_initialize_function with the set of instrumented functions.
  const symbolt &get_instrumented_functions_map_symbol();

  /// Generates instructions to initialize the instrumented function map
  /// symbol from the given set of instrumented function
  void add_instrumented_functions_map_init_instructions(
    const std::set<irep_idt> &instrumented_functions,
    goto_programt &dest);

  /// Re-generates the INITIALIZE_FUNCTION, embedding the information that
  /// functions in `instrumented_functions` have been instrumented into the
  /// goto model.
  void
  create_initialize_function(const std::set<irep_idt> &instrumented_functions);
};

#endif
