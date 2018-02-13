/*******************************************************************\

Module: Java Static Initializers

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "java_static_initializers.h"
#include "java_object_factory.h"
#include "java_utils.h"
#include <goto-programs/class_hierarchy.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/suffix.h>

// Disable linter here to allow a std::string constant, since that holds
// a length, whereas a cstr would require strlen every time.
const std::string clinit_wrapper_suffix = "::clinit_wrapper"; // NOLINT(*)
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

/// Check if function_id is a clinit wrapper
/// \param function_id: some function identifier
/// \return true if the passed identifier is a clinit wrapper
bool is_clinit_wrapper_function(const irep_idt &function_id)
{
  return has_suffix(id2string(function_id), clinit_wrapper_suffix);
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
         clinit_wrapper_name(to_symbol_type(base.type()).get_identifier())))
    {
      return true;
    }
  }

  return false;
}

/// Creates a static initializer wrapper symbol for the given class, along with
/// a global boolean that tracks if it has been run already.
/// \param class_name: class symbol name
/// \param symbol_table: global symbol table; will gain a clinit_wrapper symbol
///   and a corresponding has-run-already global.
/// \param synthetic_methods: synthetic method type map. The new clinit wrapper
///   symbol will be recorded, such that we get a callback to produce its body
///   if and when required.
static void create_clinit_wrapper_symbols(
  const irep_idt &class_name,
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods)
{
  const irep_idt &already_run_name =
    clinit_already_run_variable_name(class_name);
  symbolt already_run_symbol;
  already_run_symbol.name = already_run_name;
  already_run_symbol.pretty_name = already_run_name;
  already_run_symbol.base_name = "clinit_already_run";
  already_run_symbol.type = bool_typet();
  already_run_symbol.value = false_exprt();
  already_run_symbol.is_lvalue = true;
  already_run_symbol.is_state_var = true;
  already_run_symbol.is_static_lifetime = true;
  already_run_symbol.mode = ID_java;
  bool failed = symbol_table.add(already_run_symbol);
  INVARIANT(!failed, "clinit-already-run symbol should be fresh");

  symbolt wrapper_method_symbol;
  code_typet wrapper_method_type;
  wrapper_method_type.return_type() = void_typet();
  wrapper_method_symbol.name = clinit_wrapper_name(class_name);
  wrapper_method_symbol.pretty_name = wrapper_method_symbol.name;
  wrapper_method_symbol.base_name = "clinit_wrapper";
  wrapper_method_symbol.type = wrapper_method_type;
  // Note this use of a type-comment to provide a back-link from a method
  // to its associated class is the same one used in
  // java_bytecode_convert_methodt::convert
  wrapper_method_symbol.type.set(ID_C_class, class_name);
  wrapper_method_symbol.mode = ID_java;
  failed = symbol_table.add(wrapper_method_symbol);
  INVARIANT(!failed, "clinit-wrapper symbol should be fresh");

  auto insert_result = synthetic_methods.emplace(
    wrapper_method_symbol.name,
    synthetic_method_typet::STATIC_INITIALIZER_WRAPPER);
  INVARIANT(
    insert_result.second,
    "synthetic methods map should not already contain entry for "
    "clinit wrapper");
}

/// Produces the static initialiser wrapper body for the given function.
/// \param function_id: clinit wrapper function id (the wrapper_method_symbol
///   name created by `create_clinit_wrapper_symbols`)
/// \param symbol_table: global symbol table
/// \return the body of the static initialiser wrapper
codet get_clinit_wrapper_body(
  const irep_idt &function_id, const symbol_table_baset &symbol_table)
{
  // Assume that class C extends class C' and implements interfaces
  // I1, ..., In. We now create the following function (possibly recursively
  // creating the clinit_wrapper functions for C' and I1, ..., In):
  //
  // java::C::clinit_wrapper()
  // {
  //   if (java::C::clinit_already_run == false)
  //   {
  //     java::C::clinit_already_run = true; // before recursive calls!
  //
  //     java::C'::clinit_wrapper();
  //     java::I1::clinit_wrapper();
  //     java::I2::clinit_wrapper();
  //     // ...
  //     java::In::clinit_wrapper();
  //
  //     java::C::<clinit>();
  //   }
  // }
  const symbolt &wrapper_method_symbol = symbol_table.lookup_ref(function_id);
  irep_idt class_name = wrapper_method_symbol.type.get(ID_C_class);
  INVARIANT(
    !class_name.empty(), "wrapper function should be annotated with its class");
  const symbolt &already_run_symbol =
    symbol_table.lookup_ref(clinit_already_run_variable_name(class_name));

  equal_exprt check_already_run(
    already_run_symbol.symbol_expr(),
    false_exprt());

  // the entire body of the function is an if-then-else
  code_ifthenelset wrapper_body;

  // add the condition to the if
  wrapper_body.cond()=check_already_run;

  // add the "already-run = false" statement
  code_blockt init_body;
  code_assignt set_already_run(already_run_symbol.symbol_expr(), true_exprt());
  init_body.move_to_operands(set_already_run);

  // iterate through the base types and add recursive calls to the
  // clinit_wrapper()
  const symbolt &class_symbol = symbol_table.lookup_ref(class_name);
  for(const auto &base : to_class_type(class_symbol.type).bases())
  {
    const auto base_name = to_symbol_type(base.type()).get_identifier();
    irep_idt base_init_routine = clinit_wrapper_name(base_name);
    auto findit = symbol_table.symbols.find(base_init_routine);
    if(findit == symbol_table.symbols.end())
      continue;
    code_function_callt call_base;
    call_base.function() = findit->second.symbol_expr();
    init_body.move_to_operands(call_base);
  }

  // call java::C::<clinit>(), if the class has one static initializer
  const irep_idt &real_clinit_name = clinit_function_name(class_name);
  auto find_sym_it = symbol_table.symbols.find(real_clinit_name);
  if(find_sym_it!=symbol_table.symbols.end())
  {
    code_function_callt call_real_init;
    call_real_init.function()=find_sym_it->second.symbol_expr();
    init_body.move_to_operands(call_real_init);
  }
  wrapper_body.then_case()=init_body;

  return wrapper_body;
}

/// Create static initializer wrappers for all classes that need them.
/// \param symbol_table: global symbol table
void create_static_initializer_wrappers(
  symbol_tablet &symbol_table,
  synthetic_methods_mapt &synthetic_methods)
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
        class_identifier, symbol_table, synthetic_methods);
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
  const std::unordered_set<irep_idt, irep_id_hash> &stub_globals_set,
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

    const irep_idt class_id =
      global_symbol.type.get(ID_C_class);
    INVARIANT(
      !class_id.empty(),
      "static field should be annotated with its defining class");
    stub_globals_by_class.insert({class_id, stub_global});
  }

  // For each distinct class that has stub globals, create a clinit symbol:

  for(auto it = stub_globals_by_class.begin(),
        itend = stub_globals_by_class.end();
      it != itend;
      it = advance_to_next_key(it, itend))
  {
    const irep_idt static_init_name = clinit_function_name(it->first);

    INVARIANT(
      symbol_table.lookup_ref(it->first).type.get_bool(ID_incomplete_class),
      "only incomplete classes should be given synthetic static initialisers");
    INVARIANT(
      !symbol_table.has_symbol(static_init_name),
      "a class cannot be both incomplete, and so have stub static fields, and "
      "also define a static initializer");

    code_typet thunk_type;
    thunk_type.return_type() = void_typet();

    symbolt static_init_symbol;
    static_init_symbol.name = static_init_name;
    static_init_symbol.pretty_name = static_init_name;
    static_init_symbol.base_name = "clinit():V";
    static_init_symbol.mode = ID_java;
    static_init_symbol.type = thunk_type;
    // Note this use of a type-comment to provide a back-link from a method
    // to its associated class is the same one used in
    // java_bytecode_convert_methodt::convert
    static_init_symbol.type.set(ID_C_class, it->first);

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
/// \return synthetic static initializer body.
codet stub_global_initializer_factoryt::get_stub_initializer_body(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  const object_factory_parameterst &object_factory_parameters,
  const select_pointer_typet &pointer_type_selector)
{
  const symbolt &stub_initializer_symbol = symbol_table.lookup_ref(function_id);
  irep_idt class_id = stub_initializer_symbol.type.get(ID_C_class);
  INVARIANT(
    !class_id.empty(),
    "synthetic static initializer should be annotated with its class");
  code_blockt static_init_body;

  // Add a standard nondet initialisation for each global declared on this
  // class. Note this is the same invocation used in
  // java_static_lifetime_init.

  auto class_globals = stub_globals_by_class.equal_range(class_id);
  INVARIANT(
    class_globals.first != class_globals.second,
    "class with synthetic clinit should have at least one global to init");

  for(auto it = class_globals.first; it != class_globals.second; ++it)
  {
    const symbol_exprt new_global_symbol =
      symbol_table.lookup_ref(it->second).symbol_expr();
    gen_nondet_init(
      new_global_symbol,
      static_init_body,
      symbol_table,
      source_locationt(),
      false,
      allocation_typet::DYNAMIC,
      !is_non_null_library_global(it->second),
      object_factory_parameters,
      pointer_type_selector,
      update_in_placet::NO_UPDATE_IN_PLACE);
  }

  return static_init_body;
}
