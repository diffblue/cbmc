/*******************************************************************\

Module: Java Static Initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "java_static_initializers.h"

#include "assignments_from_json.h"
#include "ci_lazy_methods_needed.h"
#include "java_object_factory.h"
#include "java_object_factory_parameters.h"
#include "java_types.h"
#include "java_utils.h"

#include <goto-programs/class_hierarchy.h>

#include <util/arith_tools.h>
#include <util/cprover_prefix.h>
#include <util/json.h>
#include <util/std_code.h>
#include <util/suffix.h>
#include <util/symbol_table.h>

/// The three states in which a `<clinit>` method for a class can be before,
/// after, and during static class initialization. These states are only used
/// when the thread safe version of the clinit wrapper is generated.
///
/// According to the JVM Spec document (section 5.5), the JVM needs to
/// maintain, for every class initializer, a state indicating whether the
/// initializer has been executed, is being executed, or has raised errors.
/// The spec mandates that the JVM consider 4 different states (not
/// initialized, being initialized, ready for use, and initialization error).
/// The `clinit_statet` is a simplification of those 4 states where:
///
/// `NOT_INIT` corresponds to "not initialized"
/// `IN_PROGRESS` corresponds to "some thread is currently running the
///   `<clinit>` and no other thread should run it"
/// `INIT_COMPLETE` corresponds to "the `<clinit>` has been executed and the
///   class is ready to be used, or it has errored"
///
/// The last state corresponds to a fusion of the two original states "ready
/// for use" and "initialization error". The basis for fusing these states is
/// that for simplification reasons both implementations of the clinit wrapper
/// do not handle exceptions, hence the error state is not possible.
enum class clinit_statest
{
  NOT_INIT,
  IN_PROGRESS,
  INIT_COMPLETE
};

static typet clinit_states_type()
{
  return java_byte_type();
}

// Disable linter here to allow a std::string constant, since that holds
// a length, whereas a cstr would require strlen every time.
const std::string clinit_wrapper_suffix = ".<clinit_wrapper>"; // NOLINT(*)
const std::string user_specified_clinit_suffix = ".<user_specified_clinit>"; // NOLINT(*)
const std::string clinit_function_suffix = ".<clinit>:()V"; // NOLINT(*)

/// Get the Java static initializer wrapper name for a given class (the wrapper
/// checks if static initialization has already been done before invoking the
/// real static initializer if not).
/// Doesn't check whether the symbol actually exists
/// \param class_name: class symbol name
/// \return static initializer wrapper name
irep_idt clinit_wrapper_name(const irep_idt &class_name)
{
  return id2string(class_name) + clinit_wrapper_suffix;
}

irep_idt user_specified_clinit_name(const irep_idt &class_name)
{
  return id2string(class_name) + user_specified_clinit_suffix;
}

/// Check if function_id is a clinit wrapper
/// \param function_id: some function identifier
/// \return true if the passed identifier is a clinit wrapper
bool is_clinit_wrapper_function(const irep_idt &function_id)
{
  return has_suffix(id2string(function_id), clinit_wrapper_suffix);
}

/// Check if function_id is a clinit
/// \param function_id: some function identifier
/// \return true if the passed identifier is a clinit
bool is_clinit_function(const irep_idt &function_id)
{
  return has_suffix(id2string(function_id), clinit_function_suffix);
}

/// Check if function_id is a user-specified clinit
/// \param function_id: some function identifier
/// \return true if the passed identifier is a clinit
bool is_user_specified_clinit_function(const irep_idt &function_id)
{
  return has_suffix(id2string(function_id), user_specified_clinit_suffix);
}

/// Add a new symbol to the symbol table.
/// Note: assumes that a symbol with this name does not exist.
/// /param name: name of the symbol to be generated
/// /param type: type of the symbol to be generated
/// /param value: initial value of the symbol to be generated
/// /param is_thread_local: if true this symbol will be set as thread local
/// /param is_static_lifetime: if true this symbol will be set as static
/// /return returns new symbol.
static symbolt add_new_variable_symbol(
  symbol_table_baset &symbol_table,
  const irep_idt &name,
  const typet &type,
  const exprt &value,
  const bool is_thread_local,
  const bool is_static_lifetime)
{
  symbolt new_symbol;
  new_symbol.name = name;
  new_symbol.pretty_name = name;
  new_symbol.base_name = name;
  new_symbol.type = type;
  new_symbol.type.set(ID_C_no_nondet_initialization, true);
  new_symbol.value = value;
  new_symbol.is_lvalue = true;
  new_symbol.is_state_var = true;
  new_symbol.is_static_lifetime = is_static_lifetime;
  new_symbol.is_thread_local = is_thread_local;
  new_symbol.mode = ID_java;
  symbol_table.add(new_symbol);
  return new_symbol;
}

/// Get name of the static-initialization-already-done global variable for a
/// given class.
/// \param class_name: class symbol name
/// \return static initializer wrapper-already run global name
static irep_idt clinit_already_run_variable_name(const irep_idt &class_name)
{
  return id2string(class_name) + "::clinit_already_run";
}

/// Get name of the real static initializer for a given class. Doesn't check
/// if a static initializer actually exists.
/// \param class_name: class symbol name
/// \return Static initializer symbol name
static irep_idt clinit_function_name(const irep_idt &class_name)
{
  return id2string(class_name) + clinit_function_suffix;
}

/// Get name of the static-initialization-state global variable for a
/// given class.
/// \param class_name: class symbol name
/// \return static initializer wrapper-state variable global name
static irep_idt clinit_state_var_name(const irep_idt &class_name)
{
  return id2string(class_name) + CPROVER_PREFIX "clinit_state";
}

/// Get name of the static-initialization-state local state variable for a
/// given class.
/// \param class_name: class symbol name
/// \return static initializer wrapper-state local state variable name
static irep_idt clinit_thread_local_state_var_name(const irep_idt &class_name)
{
  return id2string(class_name) + CPROVER_PREFIX "clinit_threadlocal_state";
}

/// Get name of the static-initialization local variable for a given class.
/// \param class_name: class symbol name
/// \return static initializer wrapper-state local variable
static irep_idt clinit_local_init_complete_var_name(const irep_idt &class_name)
{
  return id2string(class_name) + CPROVER_PREFIX "clinit_wrapper::init_complete";
}

/// Generates a code_frontend_assignt for clinit_statest
/// /param expr:
///   expression to be used as the LHS of generated assignment.
/// /param state:
///   execution state of the clint_wrapper, used as the RHS of the generated
///   assignment.
/// /return returns a code_frontend_assignt, assigning \p expr to the integer
///   representation of \p state
static code_frontend_assignt
gen_clinit_assign(const exprt &expr, const clinit_statest state)
{
  mp_integer initv(static_cast<int>(state));
  constant_exprt init_s = from_integer(initv, clinit_states_type());
  return code_frontend_assignt(expr, init_s);
}

/// Generates an equal_exprt for clinit_statest
/// /param expr:
///   expression to be used as the LHS of generated eqaul exprt.
/// /param state:
///   execution state of the clint_wrapper, used as the RHS of the generated
///   equal exprt.
/// /return returns a equal_exprt, equating \p expr to the integer
///   representation of \p state
static equal_exprt
gen_clinit_eqexpr(const exprt &expr, const clinit_statest state)
{
  mp_integer initv(static_cast<int>(state));
  constant_exprt init_s = from_integer(initv, clinit_states_type());
  return equal_exprt(expr, init_s);
}

/// Generates codet that iterates through the base types of the class specified
/// by class_name, C, and recursively adds calls to their clinit wrapper.
/// Finally a call to the clinit of C is made. If nondet-static option was
/// given then all static variables that are not constants (i.e. final) are
/// then re-assigned to a nondet value.
/// \param symbol_table: symbol table
/// \param class_name: name of the class to generate clinit wrapper calls for
/// \param [out] init_body: appended with calls to clinit wrapper
/// \param nondet_static: true if nondet-static option was given
/// \param replace_clinit: true iff calls to clinit are replaced with calls to
///   user_specified_clinit.
/// \param object_factory_parameters: object factory parameters used to populate
///   nondet-initialized globals and objects reachable from them (only needed
///   if nondet-static is true)
/// \param pointer_type_selector: used to choose concrete types for abstract-
///   typed globals and fields (only needed if nondet-static is true)
/// \param message_handler: log
static void clinit_wrapper_do_recursive_calls(
  symbol_table_baset &symbol_table,
  const irep_idt &class_name,
  code_blockt &init_body,
  const bool nondet_static,
  const bool replace_clinit,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler)
{
  const symbolt &class_symbol = symbol_table.lookup_ref(class_name);
  for(const auto &base : to_class_type(class_symbol.type).bases())
  {
    const auto base_name = base.type().get_identifier();
    irep_idt base_init_routine = clinit_wrapper_name(base_name);
    if(const auto base_init_func = symbol_table.lookup(base_init_routine))
      init_body.add(code_function_callt{base_init_func->symbol_expr()});
  }

  const irep_idt &clinit_name = replace_clinit
                                  ? user_specified_clinit_name(class_name)
                                  : clinit_function_name(class_name);
  if(const auto clinit_func = symbol_table.lookup(clinit_name))
    init_body.add(code_function_callt{clinit_func->symbol_expr()});

  // If nondet-static option is given, add a standard nondet initialization for
  // each non-final static field of this class. Note this is the same invocation
  // used in get_stub_initializer_body and java_static_lifetime_init.
  if(nondet_static)
  {
    java_object_factory_parameterst parameters = object_factory_parameters;
    parameters.function_id = clinit_wrapper_name(class_name);

    std::vector<irep_idt> nondet_ids;
    std::for_each(
      symbol_table.symbols.begin(),
      symbol_table.symbols.end(),
      [&](const std::pair<irep_idt, symbolt> &symbol) {
        if(
          declaring_class(symbol.second) == class_name &&
          symbol.second.is_static_lifetime &&
          !symbol.second.type.get_bool(ID_C_constant))
        {
          nondet_ids.push_back(symbol.first);
        }
      });

    for(const auto &id : nondet_ids)
    {
      const symbol_exprt new_global_symbol =
        symbol_table.lookup_ref(id).symbol_expr();

      parameters.min_null_tree_depth =
        is_non_null_library_global(id)
          ? std::max(size_t(1), object_factory_parameters.min_null_tree_depth)
          : object_factory_parameters.min_null_tree_depth;

      gen_nondet_init(
        new_global_symbol,
        init_body,
        symbol_table,
        source_locationt(),
        false,
        lifetimet::DYNAMIC,
        parameters,
        pointer_type_selector,
        update_in_placet::NO_UPDATE_IN_PLACE,
        message_handler);
    }
  }
}

/// Checks whether a static initializer wrapper is needed for a given class,
/// i.e. if the given class or any superclass has a static initializer.
/// \param class_name: class symbol name
/// \param symbol_table: global symbol table
/// \return true if a static initializer wrapper is needed
static bool needs_clinit_wrapper(
  const irep_idt &class_name, const symbol_tablet &symbol_table)
{
  if(symbol_table.has_symbol(clinit_function_name(class_name)))
    return true;

  const class_typet &class_type =
    to_class_type(symbol_table.lookup_ref(class_name).type);

  for(const class_typet::baset &base : class_type.bases())
  {
    if(symbol_table.has_symbol(
         clinit_wrapper_name(base.type().get_identifier())))
    {
      return true;
    }
  }

  return false;
}

static void create_function_symbol(
  const irep_idt &class_name,
  const irep_idt &function_name,
  const irep_idt &function_base_name,
  const synthetic_method_typet &synthetic_method_type,
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods)
{
  symbolt function_symbol;
  const java_method_typet function_type({}, java_void_type());
  function_symbol.name = function_name;
  function_symbol.pretty_name = function_symbol.name;
  function_symbol.base_name = function_base_name;
  function_symbol.type = function_type;
  // This provides a back-link from a method to its associated class, as is done
  // for java_bytecode_convert_methodt::convert.
  set_declaring_class(function_symbol, class_name);
  function_symbol.mode = ID_java;
  bool failed = symbol_table.add(function_symbol);
  INVARIANT(!failed, id2string(function_base_name) + " symbol should be fresh");

  auto insert_result =
    synthetic_methods.emplace(function_symbol.name, synthetic_method_type);
  INVARIANT(
    insert_result.second,
    "synthetic methods map should not already contain entry for " +
      id2string(function_base_name));
}

// Create symbol for the "clinit_wrapper"
static void create_clinit_wrapper_function_symbol(
  const irep_idt &class_name,
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods)
{
  create_function_symbol(
    class_name,
    clinit_wrapper_name(class_name),
    "clinit_wrapper",
    synthetic_method_typet::STATIC_INITIALIZER_WRAPPER,
    symbol_table,
    synthetic_methods);
}

// Create symbol for the "user_specified_clinit"
static void create_user_specified_clinit_function_symbol(
  const irep_idt &class_name,
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods)
{
  create_function_symbol(
    class_name,
    user_specified_clinit_name(class_name),
    "user_specified_clinit",
    synthetic_method_typet::USER_SPECIFIED_STATIC_INITIALIZER,
    symbol_table,
    synthetic_methods);
}

/// Creates a static initializer wrapper symbol for the given class, along with
/// a global boolean that tracks if it has been run already.
/// \param class_name: class symbol name
/// \param symbol_table: global symbol table; will gain a clinit_wrapper symbol
///   and a corresponding has-run-already global.
/// \param synthetic_methods: synthetic method type map. The new clinit wrapper
///   symbol will be recorded, such that we get a callback to produce its body
///   if and when required.
/// \param thread_safe: if true state variables required to make the
///   clinit_wrapper thread safe will be created.
static void create_clinit_wrapper_symbols(
  const irep_idt &class_name,
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods,
  const bool thread_safe)
{
  if(thread_safe)
  {
    exprt not_init_value = from_integer(
      static_cast<int>(clinit_statest::NOT_INIT), clinit_states_type());

    // Create two global static synthetic "fields" for the class "id"
    // these two variables hold the state of the class initialization algorithm
    // across calls to the clinit_wrapper
    add_new_variable_symbol(
      symbol_table,
      clinit_state_var_name(class_name),
      clinit_states_type(),
      not_init_value,
      false,
      true);

    add_new_variable_symbol(
      symbol_table,
      clinit_thread_local_state_var_name(class_name),
      clinit_states_type(),
      not_init_value,
      true,
      true);
  }
  else
  {
    const irep_idt &already_run_name =
      clinit_already_run_variable_name(class_name);

    add_new_variable_symbol(
      symbol_table,
      already_run_name,
      bool_typet(),
      false_exprt(),
      false,
      true);
  }

  create_clinit_wrapper_function_symbol(
    class_name, symbol_table, synthetic_methods);
}

/// Thread safe version of the static initializer.
///
/// Produces the static initializer wrapper body for the given function. This
/// static initializer implements (a simplification of) the algorithm defined
/// in Section 5.5 of the JVM Specs. This function, or wrapper, checks whether
/// static init has already taken place, calls the actual `<clinit>` method if
/// not, and possibly recursively initializes super-classes and interfaces.
/// Assume that C is the class to be initialized and that C extends C' and
/// implements interfaces I1 ... In, then the algorithm is as follows:
///
/// \code
///
///   bool init_complete;
///   if(java::C::__CPROVER_PREFIX_clinit_thread_local_state == INIT_COMPLETE)
///   {
///     return;
///   }
///   java::C::__CPROVER_PREFIX_clinit_thread_local_state = INIT_COMPLETE;
///
///   // This thread atomically checks and sets the global variable
///   // 'clinit_state' in order to ensure that only this thread runs the
///   // static initializer. The assume() statement below will prevent the SAT
///   // solver from producing a thread schedule where more than 1 thread is
///   // running the initializer. At the end of this function the only
///   // thread that runs the static initializer will update the variable.
///   // Alternatively we could have done a busy wait / spin-lock, but that
///   // would achieve the same effect and blow up the size of the SAT formula.
///   ATOMIC_BEGIN
///   assume(java::C::__CPROVER_PREFIX_clinit_state != IN_PROGRESS)
///   if(java::C::__CPROVER_PREFIX_clinit_state == NOT_INIT)
///   {
///     java::C::__CPROVER_PREFIX_clinit_state = IN_PROGRESS
///     init_complete = false;
///   }
///   else if(java::C::__CPROVER_PREFIX_clinit_state == INIT_COMPLETE)
///   {
///     init_complete = true;
///   }
///   ATOMIC_END
///
///   if(init_complete)
///     return;
///
///   java::C'.<clinit_wrapper>();
///   java::I1.<clinit_wrapper>();
///   java::I2.<clinit_wrapper>();
///   // ...
///   java::In.<clinit_wrapper>();
///
///   java::C.<clinit>();  // or nondet-initialization of all static
///                        // variables of C if nondet-static is true
///
///   // Setting this variable to INIT_COMPLETE will let other threads "cross"
///   // beyond the assume() statement above in this function.
///   ATOMIC_START
///   C::__CPROVER_PREFIX_clinit_state = INIT_COMPLETE;
///   ATOMIC_END
///
///   return;
///
///  \endcode
///
/// Note: The current implementation does not deal with exceptions.
///
/// \param function_id: clinit wrapper function id (the wrapper_method_symbol
///   name created by `create_clinit_wrapper_symbols`)
/// \param symbol_table: global symbol table
/// \param nondet_static: true if nondet-static option was given
/// \param replace_clinit: true iff calls to clinit are replaced with calls to
///   user_specified_clinit.
/// \param object_factory_parameters: object factory parameters used to populate
///   nondet-initialized globals and objects reachable from them (only needed
///   if nondet-static is true)
/// \param pointer_type_selector: used to choose concrete types for abstract-
///   typed globals and fields (only needed if nondet-static is true)
/// \param message_handler: log output
/// \return the body of the static initializer wrapper
code_blockt get_thread_safe_clinit_wrapper_body(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  const bool nondet_static,
  const bool replace_clinit,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler)
{
  const symbolt &wrapper_method_symbol = symbol_table.lookup_ref(function_id);
  const auto class_name = declaring_class(wrapper_method_symbol);
  INVARIANT(class_name, "Wrapper function should have an owning class.");

  const symbolt &clinit_state_sym =
    symbol_table.lookup_ref(clinit_state_var_name(*class_name));
  const symbolt &clinit_thread_local_state_sym =
    symbol_table.lookup_ref(clinit_thread_local_state_var_name(*class_name));

  // Create a function-local variable "init_complete". This variable is used to
  // avoid inspecting the global state (clinit_state_sym) outside of
  // the critical-section.
  const symbolt &init_complete = add_new_variable_symbol(
    symbol_table,
    clinit_local_init_complete_var_name(*class_name),
    bool_typet(),
    nil_exprt(),
    true,
    false);

  code_blockt function_body;
  codet atomic_begin(ID_atomic_begin);
  codet atomic_end(ID_atomic_end);

#if 0
  // This code defines source locations for every codet generated below for
  // the static initializer wrapper. Enable this for debugging the symex going
  // through the clinit_wrapper.
  //
  // java::C.<clinit_wrapper>()
  // You will additionally need to associate the `location` with the
  // `function_body` and then manually set lines of code for each of the
  // statements of the function, using something along the lines of:
  // `mycodet.then_case().add_source_location().set_line(17);`/

  source_locationt &location = function_body.add_source_location();
  location.set_file ("<generated>");
  location.set_line ("<generated>");
  location.set_function (clinit_wrapper_name);
  std::string comment =
    "Automatically generated function. States are:\n"
    " 0 = class not initialized, init val of clinit_state/clinit_local_state\n"
    " 1 = class initialization in progress, by this or another thread\n"
    " 2 = initialization finished with success, by this or another thread\n";
  static_assert((int) clinit_statest::NOT_INIT==0, "Check commment above");
  static_assert((int) clinit_statest::IN_PROGRESS==1, "Check comment above");
  static_assert((int) clinit_statest::INIT_COMPLETE==2, "Check comment above");
#endif

  // bool init_complete;
  {
    code_declt decl(init_complete.symbol_expr());
    function_body.add(decl);
  }

  // if(C::__CPROVER_PREFIX_clinit_thread_local_state == INIT_COMPLETE) return;
  {
    code_ifthenelset conditional(
      gen_clinit_eqexpr(
        clinit_thread_local_state_sym.symbol_expr(),
        clinit_statest::INIT_COMPLETE),
      code_frontend_returnt());
    function_body.add(std::move(conditional));
  }

  // C::__CPROVER_PREFIX_clinit_thread_local_state = INIT_COMPLETE;
  {
    code_frontend_assignt assign = gen_clinit_assign(
      clinit_thread_local_state_sym.symbol_expr(),
      clinit_statest::INIT_COMPLETE);
    function_body.add(assign);
  }

  // ATOMIC_BEGIN
  {
    function_body.add(atomic_begin);
  }

  // Assume: clinit_state_sym != IN_PROGRESS
  {
    exprt assumption = gen_clinit_eqexpr(
      clinit_state_sym.symbol_expr(), clinit_statest::IN_PROGRESS);
    assumption = not_exprt(assumption);
    code_assumet assume(assumption);
    function_body.add(assume);
  }

  // If(C::__CPROVER_PREFIX_clinit_state == NOT_INIT)
  // {
  //   C::__CPROVER_PREFIX_clinit_state = IN_PROGRESS;
  //   init_complete = false;
  // }
  // else If(C::__CPROVER_PREFIX_clinit_state == INIT_COMPLETE)
  // {
  //   init_complete = true;
  // }
  {
    code_ifthenelset init_conditional(
      gen_clinit_eqexpr(
        clinit_state_sym.symbol_expr(), clinit_statest::INIT_COMPLETE),
      code_blockt(
        {code_frontend_assignt(init_complete.symbol_expr(), true_exprt())}));

    code_ifthenelset not_init_conditional(
      gen_clinit_eqexpr(
        clinit_state_sym.symbol_expr(), clinit_statest::NOT_INIT),
      code_blockt(
        {gen_clinit_assign(
           clinit_state_sym.symbol_expr(), clinit_statest::IN_PROGRESS),
         code_frontend_assignt(init_complete.symbol_expr(), false_exprt())}),
      std::move(init_conditional));

    function_body.add(std::move(not_init_conditional));
  }

  // ATOMIC_END
  {
    function_body.add(atomic_end);
  }

  // if(init_complete) return;
  {
    code_ifthenelset conditional(
      init_complete.symbol_expr(), code_frontend_returnt());
    function_body.add(std::move(conditional));
  }

  // Initialize the super-class C' and
  // the implemented interfaces l_1 ... l_n.
  // see JVMS p.359 step 7, for the exact definition of
  // the sequence l_1 to l_n.
  // This is achieved  by iterating through the base types and
  // adding recursive calls to the clinit_wrapper()
  //
  //  java::C'.<clinit_wrapper>();
  //  java::I1.<clinit_wrapper>();
  //  java::I2.<clinit_wrapper>();
  //  // ...
  //  java::In.<clinit_wrapper>();
  //
  //  java::C.<clinit>(); // or nondet-initialization of all static
  //                      // variables of C if nondet-static is true
  //
  {
    code_blockt init_body;
    clinit_wrapper_do_recursive_calls(
      symbol_table,
      *class_name,
      init_body,
      nondet_static,
      replace_clinit,
      object_factory_parameters,
      pointer_type_selector,
      message_handler);
    function_body.append(init_body);
  }

  // ATOMIC_START
  // C::__CPROVER_PREFIX_clinit_state = INIT_COMPLETE;
  // ATOMIC_END
  // return;
  {
    // synchronization prologue
    function_body.add(atomic_begin);
    function_body.add(
      gen_clinit_assign(
        clinit_state_sym.symbol_expr(), clinit_statest::INIT_COMPLETE));
    function_body.add(atomic_end);
    function_body.add(code_frontend_returnt());
  }

  return function_body;
}

/// Produces the static initializer wrapper body for the given function.
/// Note: this version of the clinit wrapper is not thread safe.
/// \param function_id: clinit wrapper function id (the wrapper_method_symbol
///   name created by `create_clinit_wrapper_symbols`)
/// \param symbol_table: global symbol table
/// \param nondet_static: true if nondet-static option was given
/// \param replace_clinit: true iff calls to clinit are replaced with calls to
///   user_specified_clinit.
/// \param object_factory_parameters: object factory parameters used to populate
///   nondet-initialized globals and objects reachable from them (only needed
///   if nondet-static is true)
/// \param pointer_type_selector: used to choose concrete types for abstract-
///   typed globals and fields (only needed if nondet-static is true)
/// \param message_handler: log output
/// \return the body of the static initializer wrapper
code_ifthenelset get_clinit_wrapper_body(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  const bool nondet_static,
  const bool replace_clinit,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler)
{
  // Assume that class C extends class C' and implements interfaces
  // I1, ..., In. We now create the following function (possibly recursively
  // creating the clinit_wrapper functions for C' and I1, ..., In):
  //
  // java::C.<clinit_wrapper>()
  // {
  //   if (!java::C::clinit_already_run)
  //   {
  //     java::C::clinit_already_run = true; // before recursive calls!
  //
  //     java::C'.<clinit_wrapper>();
  //     java::I1.<clinit_wrapper>();
  //     java::I2.<clinit_wrapper>();
  //     // ...
  //     java::In.<clinit_wrapper>();
  //
  //     java::C.<clinit>(); // or nondet-initialization of all static
  //                         // variables of C if nondet-static is true
  //   }
  // }
  const symbolt &wrapper_method_symbol = symbol_table.lookup_ref(function_id);
  const auto class_name = declaring_class(wrapper_method_symbol);
  INVARIANT(class_name, "Wrapper function should have an owning class.");

  const symbolt &already_run_symbol =
    symbol_table.lookup_ref(clinit_already_run_variable_name(*class_name));

  equal_exprt check_already_run(
    already_run_symbol.symbol_expr(),
    false_exprt());

  // add the "already-run = false" statement
  code_frontend_assignt set_already_run(
    already_run_symbol.symbol_expr(), true_exprt());
  code_blockt init_body({set_already_run});

  clinit_wrapper_do_recursive_calls(
    symbol_table,
    *class_name,
    init_body,
    nondet_static,
    replace_clinit,
    object_factory_parameters,
    pointer_type_selector,
    message_handler);

  // the entire body of the function is an if-then-else
  return code_ifthenelset(std::move(check_already_run), std::move(init_body));
}

/// \return map associating classes to the symbols they declare
std::unordered_multimap<irep_idt, symbolt>
class_to_declared_symbols(const symbol_tablet &symbol_table)
{
  std::unordered_multimap<irep_idt, symbolt> result;
  for(const auto &symbol_pair : symbol_table)
  {
    const symbolt &symbol = symbol_pair.second;
    if(optionalt<irep_idt> declaring = declaring_class(symbol))
      result.emplace(*declaring, symbol);
  }
  return result;
}

code_blockt get_user_specified_clinit_body(
  const irep_idt &class_id,
  const json_objectt &static_values_json,
  symbol_table_baset &symbol_table,
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
  size_t max_user_array_length,
  std::unordered_map<std::string, object_creation_referencet> &references,
  const std::unordered_multimap<irep_idt, symbolt>
    &class_to_declared_symbols_map)
{
  const irep_idt &real_clinit_name = clinit_function_name(class_id);
  const auto clinit_func = symbol_table.lookup(real_clinit_name);
  if(clinit_func == nullptr)
  {
    // Case where the real clinit doesn't appear in the symbol table, even
    // though their is user specifed one. This may occur when some class
    // substitution happened after compilation.
    return code_blockt{};
  }
  const auto class_entry =
    static_values_json.find(id2string(strip_java_namespace_prefix(class_id)));
  if(class_entry != static_values_json.end() && class_entry->second.is_object())
  {
    const auto &class_json_object = to_json_object(class_entry->second);
    std::map<symbol_exprt, jsont> static_field_values;
    for(const auto &symbol_pair :
        equal_range(class_to_declared_symbols_map, class_id))
    {
      const symbolt &symbol = symbol_pair.second;
      if(symbol.is_static_lifetime)
      {
        const symbol_exprt &static_field_expr = symbol.symbol_expr();
        const auto &static_field_entry =
          class_json_object.find(id2string(symbol.base_name));
        if(static_field_entry != class_json_object.end())
        {
          static_field_values.insert(
            {static_field_expr, static_field_entry->second});
        }
      }
    }
    code_with_references_listt code_with_references;
    for(const auto &value_pair : static_field_values)
    {
      code_with_references.append(assign_from_json(
        value_pair.first,
        value_pair.second,
        real_clinit_name,
        symbol_table,
        needed_lazy_methods,
        max_user_array_length,
        references));
    }
    code_with_referencest::reference_substitutiont reference_substitution =
      [&](const std::string &reference_id) -> object_creation_referencet & {
      auto it = references.find(reference_id);
      INVARIANT(it != references.end(), "reference id must be present in map");
      return it->second;
    };
    code_blockt body;
    for(const auto &code_with_ref : code_with_references.list)
      body.append(code_with_ref->to_code(reference_substitution));
    return body;
  }
  return code_blockt{{code_function_callt{clinit_func->symbol_expr()}}};
}

/// Create static initializer wrappers and possibly user-specified functions for
/// initial static field value assignments for all classes that need them.
/// For each class that will require a static initializer wrapper, create a
/// function named package.classname.\<clinit_wrapper\>, and a corresponding
/// global tracking whether it has run or not. If a file containing initial
/// static values is given, also create a function named
/// package.classname::user_specified_clinit.
/// \param symbol_table: global symbol table
/// \param synthetic_methods: synthetic methods map. Will be extended noting
///   that any wrapper belongs to this code, and so `get_clinit_wrapper_body`
///   should be used to produce the method body when required.
/// \param thread_safe: if true state variables required to make the
///   clinit_wrapper thread safe will be created.
/// \param is_user_clinit_needed: determines whether or not a symbol for the
///   synthetic user_specified_clinit function should be created. This is true
///   if a file was given with the --static-values option and false otherwise.
void create_static_initializer_symbols(
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods,
  const bool thread_safe,
  const bool is_user_clinit_needed)
{
  // Top-sort the class hierarchy, such that we visit parents before children,
  // and can so identify parents that need static initialisation by whether we
  // have made them a clinit_wrapper method.
  class_hierarchy_grapht class_graph;
  class_graph.populate(symbol_table);
  std::list<class_hierarchy_grapht::node_indext> topsorted_nodes =
    class_graph.topsort();

  for(const auto node : topsorted_nodes)
  {
    const irep_idt &class_identifier = class_graph[node].class_identifier;
    if(needs_clinit_wrapper(class_identifier, symbol_table))
    {
      create_clinit_wrapper_symbols(
        class_identifier, symbol_table, synthetic_methods, thread_safe);
      if(is_user_clinit_needed)
      {
        create_user_specified_clinit_function_symbol(
          class_identifier, symbol_table, synthetic_methods);
      }
    }
  }
}

/// Advance map iterator to next distinct key
/// \param in: iterator to advance
/// \param end: end of container iterator
template<class itertype>
static itertype advance_to_next_key(itertype in, itertype end)
{
  PRECONDITION(in != end);
  auto initial_key = in->first;
  while(in != end && in->first == initial_key)
    ++in;
  return in;
}

/// Create static initializer symbols for each distinct class that has stub
/// globals.
/// \param symbol_table: global symbol table. Will gain static initializer
///   method symbols for each class that has a stub global in `stub_globals_set`
/// \param stub_globals_set: set of stub global symbols
/// \param synthetic_methods: map of synthetic method types. We record the new
///   static initialiser such that we get a callback to provide its body as and
///   when it is required.
void stub_global_initializer_factoryt::create_stub_global_initializer_symbols(
  symbol_tablet &symbol_table,
  const std::unordered_set<irep_idt> &stub_globals_set,
  synthetic_methods_mapt &synthetic_methods)
{
  // Populate map from class id -> stub globals:
  for(const irep_idt &stub_global : stub_globals_set)
  {
    const symbolt &global_symbol = symbol_table.lookup_ref(stub_global);
    if(global_symbol.value.is_nil())
    {
      // This symbol is already nondet-initialised during __CPROVER_initialize
      // (generated in java_static_lifetime_init). In future this will only
      // be the case for primitive-typed fields, but for now reference-typed
      // fields can also be treated this way in the exceptional case that they
      // belong to a non-stub class. Skip the field, as it does not need a
      // synthetic static initializer.
      continue;
    }

    const auto class_id = declaring_class(global_symbol);
    INVARIANT(class_id, "Static field should have a defining class.");
    stub_globals_by_class.insert({*class_id, stub_global});
  }

  // For each distinct class that has stub globals, create a clinit symbol:

  for(auto it = stub_globals_by_class.begin(),
        itend = stub_globals_by_class.end();
      it != itend;
      it = advance_to_next_key(it, itend))
  {
    const irep_idt static_init_name = clinit_function_name(it->first);

    INVARIANT(
      to_java_class_type(symbol_table.lookup_ref(it->first).type).get_is_stub(),
      "only stub classes should be given synthetic static initialisers");
    INVARIANT(
      !symbol_table.has_symbol(static_init_name),
      "a class cannot be both incomplete, and so have stub static fields, and "
      "also define a static initializer");

    const java_method_typet thunk_type({}, java_void_type());

    symbolt static_init_symbol;
    static_init_symbol.name = static_init_name;
    static_init_symbol.pretty_name = static_init_name;
    static_init_symbol.base_name = "clinit():V";
    static_init_symbol.mode = ID_java;
    static_init_symbol.type = thunk_type;
    // This provides a back-link from a method to its associated class, as is
    // done for java_bytecode_convert_methodt::convert.
    set_declaring_class(static_init_symbol, it->first);

    bool failed = symbol_table.add(static_init_symbol);
    INVARIANT(!failed, "symbol should not already exist");

    auto insert_result = synthetic_methods.emplace(
      static_init_symbol.name,
      synthetic_method_typet::STUB_CLASS_STATIC_INITIALIZER);
    INVARIANT(
      insert_result.second,
      "synthetic methods map should not already contain entry for "
      "stub static initializer");
  }
}

/// Create the body of a synthetic static initializer (clinit method),
/// which initialise stub globals in the same manner as
/// java_static_lifetime_init, only delayed until first reference by virtue of
/// being given in a static initializer rather than directly in
/// __CPROVER_initialize.
/// \param function_id: synthetic static initializer id
/// \param symbol_table: global symbol table; may gain local variables created
///   for the new static initializer
/// \param object_factory_parameters: object factory parameters used to populate
///   the stub globals and objects reachable from them
/// \param pointer_type_selector: used to choose concrete types for abstract-
///   typed globals and fields.
/// \param message_handler: log output
/// \return synthetic static initializer body.
code_blockt stub_global_initializer_factoryt::get_stub_initializer_body(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  const java_object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler)
{
  const symbolt &stub_initializer_symbol = symbol_table.lookup_ref(function_id);
  const auto class_id = declaring_class(stub_initializer_symbol);
  INVARIANT(
    class_id, "Synthetic static initializer should have an owning class.");
  code_blockt static_init_body;

  // Add a standard nondet initialisation for each global declared on this
  // class. Note this is the same invocation used in
  // java_static_lifetime_init.

  auto class_globals = equal_range(stub_globals_by_class, *class_id);
  INVARIANT(
    !class_globals.empty(),
    "class with synthetic clinit should have at least one global to init");

  java_object_factory_parameterst parameters = object_factory_parameters;
  parameters.function_id = function_id;

  for(const auto &pair : class_globals)
  {
    const symbol_exprt new_global_symbol =
      symbol_table.lookup_ref(pair.second).symbol_expr();

    parameters.min_null_tree_depth =
      is_non_null_library_global(pair.second)
        ? object_factory_parameters.min_null_tree_depth + 1
        : object_factory_parameters.min_null_tree_depth;

    source_locationt location;
    location.set_function(function_id);
    gen_nondet_init(
      new_global_symbol,
      static_init_body,
      symbol_table,
      location,
      false,
      lifetimet::DYNAMIC,
      parameters,
      pointer_type_selector,
      update_in_placet::NO_UPDATE_IN_PLACE,
      message_handler);
  }

  return static_init_body;
}
