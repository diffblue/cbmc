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

using build_argumentst =
  std::function<std::pair<code_blockt, std::vector<exprt>>(
    const symbolt &function,
    symbol_table_baset &symbol_table)>;

/// Given the \p symbol_table and the \p main_class to test, this function
/// generates a new function __CPROVER__start that calls the method under tests.
///
/// If __CPROVER__start is already in the `symbol_table`, it silently returns.
/// Otherwise it finds the method under test using `get_main_symbol` and
/// constructs a body for __CPROVER__start which does as follows:
///
/// 1. Allocates and initializes the parameters of the method under test.
/// 2. Call it and save its return variable in the variable 'return'.
/// 3. Declare variable 'return' as an output variable using a `code_outputt`,
///    together with other objects possibly altered by the execution of
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
/// \param symbol_table: Global symbol table
/// \param main_class: Identifier of a class within which the main method to be
///   analysed exists. This may be empty if the intention is not to analyse the
///   main method.
/// \param message_handler: Where to write output to.
/// \param assume_init_pointers_not_null: If this is true then any reference
///   type parameters to the function under tests are assumed to be non-null.
/// \param assert_uncaught_exceptions: Add an uncaught-exception check.
/// \param object_factory_parameters: Parameters for creation of arguments.
/// \param pointer_type_selector: Logic for substituting types of pointers.
/// \param string_refinement_enabled: If true, string refinement's string data
///   structure will also be initialised and added to the symbol table.
/// \param build_arguments: The function which builds the `codet`s which
///   initialise the arguments for a function.
/// \return true if error occurred on entry point search
bool java_entry_point(
  class symbol_table_baset &symbol_table,
  const irep_idt &main_class,
  class message_handlert &message_handler,
  bool assume_init_pointers_not_null,
  bool assert_uncaught_exceptions,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  bool string_refinement_enabled,
  const build_argumentst &build_arguments);

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
/// \param assert_uncaught_exceptions: Add an uncaught-exception check
/// \param object_factory_parameters: Parameters for creation of arguments
/// \param pointer_type_selector: Logic for substituting types of pointers
/// \param build_arguments: The function which builds the `codet`s which
///   initialise the arguments for a function.
/// \return true if error occurred on entry point search, false otherwise
bool generate_java_start_function(
  const symbolt &symbol,
  class symbol_table_baset &symbol_table,
  class message_handlert &message_handler,
  bool assert_uncaught_exceptions,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  const build_argumentst &build_arguments);

/// \param function: The function under test, for which to build the arguments.
/// \param symbol_table: For the purposes of adding any local variables
///   generated or any functions which are generated and called.
/// \param assume_init_pointers_not_null: If this is true then any reference
///   type parameters to the function under tests are assumed to be non-null.
/// \param object_factory_parameters: Configuration of the object factory.
/// \param pointer_type_selector: Means of selecting the type of value
///   constructed for reference types which are initialised by the code
///   returned.
/// \param message_handler: log
/// \returns A pairing of the code to initialise the arguments and a std::vector
///   of the expressions for these arguments. The vector contains one element
///   per parameter of \p function. The vector of expressions can be used as
///   arguments for \p function. The code returned allocates the objects used as
///   test arguments for the function under test (\p function) and
///   non-deterministically initializes them. This code returned must be placed
///   into the code block of the function call, before the function call.
///   Typically this code block would be  __CPROVER__start.
std::pair<code_blockt, std::vector<exprt>> java_build_arguments(
  const symbolt &function,
  symbol_table_baset &symbol_table,
  bool assume_init_pointers_not_null,
  java_object_factory_parameterst object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler);

/// Adds `__cprover_initialize` to the \p symbol_table but does not generate
/// code for it yet.
void create_java_initialize(symbol_table_baset &symbol_table);

/// Adds the body to __CPROVER_initialize
void java_static_lifetime_init(
  symbol_table_baset &symbol_table,
  const source_locationt &source_location,
  bool assume_init_pointers_not_null,
  java_object_factory_parameterst object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  bool string_refinement_enabled,
  message_handlert &message_handler);

#endif // CPROVER_JAVA_BYTECODE_JAVA_ENTRY_POINT_H
