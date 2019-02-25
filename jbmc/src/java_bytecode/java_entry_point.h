/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H
#define CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H

#include "java_bytecode_language.h"
#include "select_pointer_type.h"

#include <util/irep.h>
#include <util/symbol.h>

#define JAVA_ENTRY_POINT_RETURN_SYMBOL "return'"
#define JAVA_ENTRY_POINT_EXCEPTION_SYMBOL "uncaught_exception'"

/// Given the \p symbol_table and the \p main_class to test, this function
/// generates a new function __CPROVER__start that calls the method under tests.
///
/// If __CPROVER__start is already in the `symbol_table`, it silently returns.
/// Otherwise it finds the method under test using `get_main_symbol` and
/// constructs a body for __CPROVER__start which does as follows:
///
/// 1. Allocates and initializes the parameters of the method under test.
/// 2. Call it and save its return variable in the variable 'return'.
/// 3. Declare variable 'return' as an output variable (codet with id
///    ID_output), together with other objects possibly altered by the execution
///    the method under test (in `java_record_outputs`)
///
/// When \p assume_init_pointers_not_null is false, the generated parameter
/// initialization code will non-deterministically set input parameters to
/// either null or a stack-allocated object. Observe that the null/non-null
/// setting only applies to the parameter itself, and is not propagated to other
/// pointers that it might be necessary to initialize in the object tree rooted
/// at the parameter.
/// Parameter \p max_nondet_array_length provides the maximum length for an
/// array used as part of the input to the method under test, and
/// \p max_nondet_tree_depth defines the maximum depth of the object tree
/// created for such inputs. This maximum depth is used **in conjunction** with
/// the so-called "recursive type set" (see field `recursive_set` in class
/// java_object_factoryt) to bound the depth of the object tree for the
/// parameter. Only when
/// - the depth of the tree is >= max_nondet_tree_depth **AND**
/// - the type of the object under initialization is already found in the
///   recursive set
/// then that object is not initalized and the reference pointing to it is
/// (deterministically) set to null. This is a source of underapproximation in
/// our approach to test generation, and should perhaps be fixed in the future.
///
/// \return true if error occurred on entry point search
bool java_entry_point(
  class symbol_table_baset &symbol_table,
  const irep_idt &main_class,
  class message_handlert &message_handler,
  bool assume_init_pointers_not_null,
  bool assert_uncaught_exceptions,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  bool string_refinement_enabled);

struct main_function_resultt
{
  enum statust
  {
    Success,
    Error,
    NotFound
  } status;
  symbolt main_function;

  // Implicit conversion doesn't lose information and allows return of status
  // NOLINTNEXTLINE(runtime/explicit)
  main_function_resultt(statust status) : status(status)
  {
  }

  // Implicit conversion doesn't lose information and allows return of symbol
  // NOLINTNEXTLINE(runtime/explicit)
  main_function_resultt(const symbolt &main_function)
    : status(Success), main_function(main_function)
  {
  }

  bool is_success() const
  {
    return status == Success;
  }
  bool is_error() const
  {
    return status == Error;
  }
};

/// Get the symbol name of java.lang.Class' initializer method. This method
/// should initialize a Class instance with known properties of the type it
/// represents, such as its name, whether it is abstract, or an enumeration,
/// etc. The method may or may not exist in any particular symbol table; it is
/// up to the caller to check.
/// The method's Java signature is:
/// void cproverInitializeClassLiteral(
///   String name,
///   boolean isAnnotation,
///   boolean isArray,
///   boolean isInterface,
///   boolean isSynthetic,
///   boolean isLocalClass,
///   boolean isMemberClass,
///   boolean isEnum);
/// \return Class initializer method's symbol name.
irep_idt get_java_class_literal_initializer_signature();

/// Figures out the entry point of the code to verify
main_function_resultt get_main_symbol(
  const symbol_table_baset &symbol_table,
  const irep_idt &main_class,
  message_handlert &);

/// Generate a _start function for a specific function. See
/// java_entry_point for more details.
/// \param symbol: The symbol representing the function to call
/// \param symbol_table: Global symbol table
/// \param message_handler: Where to write output to
/// \param assume_init_pointers_not_null: When creating pointers, assume they
///   always take a non-null value.
/// \param assert_uncaught_exceptions: Add an uncaught-exception check
/// \param object_factory_parameters: Parameters for creation of arguments
/// \param pointer_type_selector: Logic for substituting types of pointers
/// \return true if error occurred on entry point search, false otherwise
bool generate_java_start_function(
  const symbolt &symbol,
  class symbol_table_baset &symbol_table,
  class message_handlert &message_handler,
  bool assume_init_pointers_not_null,
  bool assert_uncaught_exceptions,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector);

#endif // CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H
