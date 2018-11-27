/*******************************************************************\

 Module: Java Bytecode

 Author: Diffblue Ltd.

\*******************************************************************/

#include "ci_lazy_methods.h"
#include "java_entry_point.h"
#include "java_class_loader.h"
#include "java_utils.h"
#include "java_string_library_preprocess.h"
#include "remove_exceptions.h"

#include <util/expr_iterator.h>
#include <util/suffix.h>

#include <goto-programs/resolve_inherited_component.h>

/// Constructor for lazy-method loading
/// \param symbol_table: the symbol table to use
/// \param main_class: identifier of the entry point / main class
/// \param main_jar_classes: specify main class of jar if \p main_class is empty
/// \param lazy_methods_extra_entry_points: entry point functions to use
/// \param java_class_loader: the Java class loader to use
/// \param extra_instantiated_classes: list of class identifiers which are
///   considered to be required and therefore their methods should not be
///   removed via `lazy-methods`. Example of use: `ArrayList` as general
///   implementation for `List` interface.
/// \param pointer_type_selector: selector to handle correct pointer types
/// \param message_handler: the message handler to use for output
/// \param synthetic_methods: map from synthetic method names to the type of
///   synthetic method (e.g. stub class static initialiser). Indicates that
///   these method bodies are produced internally, rather than generated from
///   Java bytecode.
ci_lazy_methodst::ci_lazy_methodst(
  const symbol_tablet &symbol_table,
  const irep_idt &main_class,
  const std::vector<irep_idt> &main_jar_classes,
  const std::vector<load_extra_methodst> &lazy_methods_extra_entry_points,
  java_class_loadert &java_class_loader,
  const std::vector<irep_idt> &extra_instantiated_classes,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler,
  const synthetic_methods_mapt &synthetic_methods)
  : messaget(message_handler),
    main_class(main_class),
    main_jar_classes(main_jar_classes),
    lazy_methods_extra_entry_points(lazy_methods_extra_entry_points),
    java_class_loader(java_class_loader),
    extra_instantiated_classes(extra_instantiated_classes),
    pointer_type_selector(pointer_type_selector),
    synthetic_methods(synthetic_methods)
{
  // build the class hierarchy
  class_hierarchy(symbol_table);
}

/// Checks if an expression refers to any class literals (e.g. MyType.class)
/// These are expressed as ldc instructions in Java bytecode, and as symbols
/// of the form `MyType@class_model` in GOTO programs.
/// \param expr: expression to check
/// \return true if the expression or any of its subexpressions refer to a
///   class
static bool references_class_model(const exprt &expr)
{
  static const symbol_typet class_type("java::java.lang.Class");

  for(auto it = expr.depth_begin(); it != expr.depth_end(); ++it)
  {
    if(can_cast_expr<symbol_exprt>(*it) &&
       it->type() == class_type &&
       has_suffix(
         id2string(to_symbol_expr(*it).get_identifier()),
         JAVA_CLASS_MODEL_SUFFIX))
    {
      return true;
    }
  }

  return false;
}

/// Uses a simple context-insensitive ('ci') analysis to determine which methods
/// may be reachable from the main entry point. In brief, static methods are
/// reachable if we find a callsite in another reachable site, while virtual
/// methods are reachable if we find a virtual callsite targeting a compatible
/// type *and* a constructor callsite indicating an object of that type may be
/// instantiated (or evidence that an object of that type exists before the main
/// function is entered, such as being passed as a parameter).
/// Elaborates lazily-converted methods that may be reachable starting
/// from the main entry point (usually provided with the --function command-
/// line option
/// \param symbol_table: global symbol table
/// \param [out] method_bytecode: map from method names to relevant symbol and
///   parsed-method objects.
/// \param method_converter: Function for converting methods on demand.
/// \return Returns false on success
bool ci_lazy_methodst::operator()(
  symbol_tablet &symbol_table,
  method_bytecodet &method_bytecode,
  const method_convertert &method_converter)
{
  std::unordered_set<irep_idt> methods_to_convert_later =
    entry_point_methods(symbol_table);

  // Add any extra entry points specified; we should elaborate these in the
  // same way as the main function.
  for(const auto &extra_function_generator : lazy_methods_extra_entry_points)
  {
    std::vector<irep_idt> extra_methods =
      extra_function_generator(symbol_table);
    methods_to_convert_later.insert(extra_methods.begin(), extra_methods.end());
  }

  std::unordered_set<irep_idt> instantiated_classes;

  {
    std::unordered_set<irep_idt> initial_callable_methods;
    ci_lazy_methods_neededt initial_lazy_methods(
      initial_callable_methods,
      instantiated_classes,
      symbol_table,
      pointer_type_selector);
    initialize_instantiated_classes(
      methods_to_convert_later, namespacet(symbol_table), initial_lazy_methods);
    methods_to_convert_later.insert(
      initial_callable_methods.begin(), initial_callable_methods.end());
  }

  std::unordered_set<irep_idt> methods_already_populated;
  std::unordered_set<exprt, irep_hash> virtual_function_calls;
  bool class_initializer_seen = false;

  bool any_new_classes = true;
  while(any_new_classes)
  {
    bool any_new_methods = true;
    while(any_new_methods)
    {
      any_new_methods = false;
      while(!methods_to_convert_later.empty())
      {
        std::unordered_set<irep_idt> methods_to_convert;
        std::swap(methods_to_convert, methods_to_convert_later);
        for(const auto &mname : methods_to_convert)
        {
          const auto conversion_result = convert_and_analyze_method(
            method_converter,
            methods_already_populated,
            class_initializer_seen,
            mname,
            symbol_table,
            methods_to_convert_later,
            instantiated_classes,
            virtual_function_calls);
          any_new_methods |= conversion_result.new_method_seen;
          class_initializer_seen |= conversion_result.class_initializer_seen;
        }
      }

      // Given the object types we now know may be created, populate more
      // possible virtual function call targets:

      debug() << "CI lazy methods: add virtual method targets ("
              << virtual_function_calls.size() << " callsites)" << eom;

      for(const exprt &function : virtual_function_calls)
      {
        get_virtual_method_targets(
          function,
          instantiated_classes,
          methods_to_convert_later,
          symbol_table);
      }
    }

    any_new_classes = handle_virtual_methods_with_no_callees(
      methods_to_convert_later,
      instantiated_classes,
      virtual_function_calls,
      symbol_table);
  }

  // Remove symbols for methods that were declared but never used:
  symbol_tablet keep_symbols;
  // Manually keep @inflight_exception, as it is unused at this stage
  // but will become used when the `remove_exceptions` pass is run:
  keep_symbols.add(symbol_table.lookup_ref(INFLIGHT_EXCEPTION_VARIABLE_NAME));

  for(const auto &sym : symbol_table.symbols)
  {
    // Don't keep global variables (unless they're gathered below from a
    // function that references them)
    if(sym.second.is_static_lifetime)
      continue;
    if(sym.second.type.id()==ID_code)
    {
      // Don't keep functions that belong to this language that we haven't
      // converted above
      if(
        (method_bytecode.contains_method(sym.first) ||
         synthetic_methods.count(sym.first)) &&
        !methods_already_populated.count(sym.first))
      {
        continue;
      }
      // If this is a function then add all the things used in it
      gather_needed_globals(sym.second.value, symbol_table, keep_symbols);
    }
    keep_symbols.add(sym.second);
  }

  debug() << "CI lazy methods: removed "
          << symbol_table.symbols.size() - keep_symbols.symbols.size()
          << " unreachable methods and globals" << eom;

  symbol_table.swap(keep_symbols);

  return false;
}

/// Look for virtual callsites with no candidate targets. If we have
/// invokevirtual A.f and we don't believe either A or any of its children
/// may exist, we assume specifically A is somehow instantiated. Note this
/// may result in an abstract class being classified as instantiated, which
/// stands in for some unknown concrete subclass: in this case the called
/// method will be a stub.
/// \return whether a new class was encountered
bool ci_lazy_methodst::handle_virtual_methods_with_no_callees(
  std::unordered_set<irep_idt> &methods_to_convert_later,
  std::unordered_set<irep_idt> &instantiated_classes,
  const std::unordered_set<exprt, irep_hash> &virtual_function_calls,
  symbol_tablet &symbol_table)
{
  ci_lazy_methods_neededt lazy_methods_loader(
    methods_to_convert_later,
    instantiated_classes,
    symbol_table,
    pointer_type_selector);

  bool any_new_classes = false;
  for(const exprt &virtual_function_call : virtual_function_calls)
  {
    std::unordered_set<irep_idt> candidate_target_methods;
    get_virtual_method_targets(
      virtual_function_call,
      instantiated_classes,
      candidate_target_methods,
      symbol_table);

    if(!candidate_target_methods.empty())
      continue;

    // Add the call class to instantiated_classes and assert that it
    // didn't already exist
    const irep_idt &call_class = virtual_function_call.get(ID_C_class);
    bool added_class = instantiated_classes.count(call_class) == 0;
    CHECK_RETURN(added_class);

    lazy_methods_loader.add_all_needed_classes(
      to_pointer_type(
        to_java_method_type(virtual_function_call.type()).get_this()->type()));
    any_new_classes = true;

    // Check that `get_virtual_method_target` returns a method now
    const irep_idt &call_basename =
      virtual_function_call.get(ID_component_name);
    const irep_idt method_name = get_virtual_method_target(
      instantiated_classes, call_basename, call_class, symbol_table);
    CHECK_RETURN(!method_name.empty());

    // Add what it returns to methods_to_convert_later
    methods_to_convert_later.insert(method_name);
  }
  return any_new_classes;
}

/// Convert a method, add it to the populated set, add needed methods to
/// methods_to_convert_later and add virtual calls from the method to
/// virtual_function_calls
/// \return structure containing two Booleans:
///     * class_initializer_seen which is true if the class_initializer_seen
///       argument was false and the class_model is referenced in
///       the body of the method
///     * new_method_seen if the method was not converted before and was
///       converted successfully here
ci_lazy_methodst::convert_method_resultt
ci_lazy_methodst::convert_and_analyze_method(
  const method_convertert &method_converter,
  std::unordered_set<irep_idt> &methods_already_populated,
  const bool class_initializer_already_seen,
  const irep_idt &method_name,
  symbol_tablet &symbol_table,
  std::unordered_set<irep_idt> &methods_to_convert_later,
  std::unordered_set<irep_idt> &instantiated_classes,
  std::unordered_set<exprt, irep_hash> &virtual_function_calls)
{
  convert_method_resultt result;
  if(!methods_already_populated.insert(method_name).second)
    return result;

  debug() << "CI lazy methods: elaborate " << method_name << eom;

  // Note this wraps *references* to methods_to_convert_later &
  // instantiated_classes
  ci_lazy_methods_neededt needed_methods(
    methods_to_convert_later,
    instantiated_classes,
    symbol_table,
    pointer_type_selector);

  if(method_converter(method_name, needed_methods))
    return result;

  const exprt &method_body = symbol_table.lookup_ref(method_name).value;
  gather_virtual_callsites(method_body, virtual_function_calls);

  if(!class_initializer_already_seen && references_class_model(method_body))
  {
    result.class_initializer_seen = true;
    const irep_idt initializer_signature =
      get_java_class_literal_initializer_signature();
    if(symbol_table.has_symbol(initializer_signature))
      methods_to_convert_later.insert(initializer_signature);
  }
  result.new_method_seen = true;
  return result;
}

/// Entry point methods are either:
///   * the "main" function of the `main_class` if it exists
///   * all the methods of the main class if it is not empty
///   * all the methods of the main jar file
/// \return set of identifiers of entry point methods
std::unordered_set<irep_idt>
ci_lazy_methodst::entry_point_methods(const symbol_tablet &symbol_table)
{
  std::unordered_set<irep_idt> methods_to_convert_later;

  const main_function_resultt main_function = get_main_symbol(
    symbol_table, this->main_class, this->get_message_handler());
  if(!main_function.is_success())
  {
    // Failed, mark all functions in the given main class(es)
    // reachable.
    std::vector<irep_idt> reachable_classes;
    if(!this->main_class.empty())
      reachable_classes.push_back(this->main_class);
    else
      reachable_classes = this->main_jar_classes;
    for(const irep_idt &class_name : reachable_classes)
    {
      const auto &methods =
        this->java_class_loader.get_original_class(class_name)
          .parsed_class.methods;
      for(const auto &method : methods)
      {
        const irep_idt methodid = "java::" + id2string(class_name) + "." +
                                  id2string(method.name) + ":" +
                                  id2string(method.descriptor);
        methods_to_convert_later.insert(methodid);
      }
    }
  }
  else
    methods_to_convert_later.insert(main_function.main_function.name);
  return methods_to_convert_later;
}

/// Build up a list of methods whose type may be passed around reachable
/// from the entry point.
/// \param entry_points: list of fully-qualified function names that
///   we should assume are reachable
/// \param ns: global namespace
/// \param [out] needed_lazy_methods: Populated with all Java reference types
///   whose references may be passed, directly or indirectly, to any of the
///   functions in `entry_points`.
void ci_lazy_methodst::initialize_instantiated_classes(
  const std::unordered_set<irep_idt> &entry_points,
  const namespacet &ns,
  ci_lazy_methods_neededt &needed_lazy_methods)
{
  for(const auto &mname : entry_points)
  {
    const auto &symbol=ns.lookup(mname);
    const auto &mtype = to_java_method_type(symbol.type);
    for(const auto &param : mtype.parameters())
    {
      if(param.type().id()==ID_pointer)
      {
        const pointer_typet &original_pointer = to_pointer_type(param.type());
        needed_lazy_methods.add_all_needed_classes(original_pointer);
      }
    }
  }

  // Also add classes whose instances are magically
  // created by the JVM and so won't be spotted by
  // looking for constructors and calls as usual:
  needed_lazy_methods.add_needed_class("java::java.lang.String");
  needed_lazy_methods.add_needed_class("java::java.lang.Class");
  needed_lazy_methods.add_needed_class("java::java.lang.Object");

  // As in class_loader, ensure these classes stay available
  for(const auto &id : extra_instantiated_classes)
    needed_lazy_methods.add_needed_class("java::" + id2string(id));
}

/// Get places where virtual functions are called.
/// \param e: expression tree to search
/// \param [out] result: filled with pointers to each function call within
///   e that calls a virtual function.
void ci_lazy_methodst::gather_virtual_callsites(
  const exprt &e,
  std::unordered_set<exprt, irep_hash> &result)
{
  if(e.id()!=ID_code)
    return;
  const codet &c=to_code(e);
  if(c.get_statement()==ID_function_call &&
     to_code_function_call(c).function().id()==ID_virtual_function)
  {
    result.insert(to_code_function_call(c).function());
  }
  else
  {
    for(const exprt &op : e.operands())
      gather_virtual_callsites(op, result);
  }
}

/// Find possible callees, excluding types that are not known to be
/// instantiated.
/// \param called_function: virtual function call whose concrete function calls
///   should be determined.
/// \param instantiated_classes: set of classes that can be instantiated. Any
///   potential callee not in this set will be ignored.
/// \param [out] callable_methods: Populated with all possible `c` callees,
///   taking `instantiated_classes` into account (virtual function overrides
///   defined on classes that are not 'needed' are ignored)
/// \param symbol_table: global symbol table
void ci_lazy_methodst::get_virtual_method_targets(
  const exprt &called_function,
  const std::unordered_set<irep_idt> &instantiated_classes,
  std::unordered_set<irep_idt> &callable_methods,
  symbol_tablet &symbol_table)
{
  PRECONDITION(called_function.id()==ID_virtual_function);

  const auto &call_class=called_function.get(ID_C_class);
  INVARIANT(
    !call_class.empty(), "All virtual calls should be aimed at a class");
  const auto &call_basename=called_function.get(ID_component_name);
  INVARIANT(
    !call_basename.empty(),
    "Virtual function must have a reasonable name after removing class");

  class_hierarchyt::idst self_and_child_classes =
    class_hierarchy.get_children_trans(call_class);
  self_and_child_classes.push_back(call_class);

  for(const irep_idt &class_name : self_and_child_classes)
  {
    const irep_idt method_name = get_virtual_method_target(
      instantiated_classes, call_basename, class_name, symbol_table);
    if(!method_name.empty())
      callable_methods.insert(method_name);
  }
}

/// See output
/// \param e: expression tree to search
/// \param symbol_table: global symbol table
/// \param [out] needed: Populated with global variable symbols referenced from
/// `e` or its children.
void ci_lazy_methodst::gather_needed_globals(
  const exprt &e,
  const symbol_tablet &symbol_table,
  symbol_tablet &needed)
{
  if(e.id()==ID_symbol)
  {
    // If the symbol isn't in the symbol table at all, then it is defined
    // on an opaque type (i.e. we don't have the class definition at this point)
    // and will be created during the typecheck phase.
    // We don't mark it as 'needed' as it doesn't exist yet to keep.
    const auto findit=
      symbol_table.symbols.find(to_symbol_expr(e).get_identifier());
    if(findit!=symbol_table.symbols.end() &&
       findit->second.is_static_lifetime)
    {
      needed.add(findit->second);
      // Gather any globals referenced in the initialiser:
      gather_needed_globals(findit->second.value, symbol_table, needed);
    }
  }
  else
    forall_operands(opit, e)
      gather_needed_globals(*opit, symbol_table, needed);
}

/// Find a virtual callee, if one is defined and the callee type is known to
/// exist.
/// \param instantiated_classes: set of classes that can be instantiated.
///   Any potential callee not in this set will be ignored.
/// \param call_basename: unqualified function name with type signature (e.g.
///   "f:(I)")
/// \param classname: class name that may define or override a function named
///   `call_basename`.
/// \param symbol_table: global symtab
/// \return Returns the fully qualified name of `classname`'s definition of
///   `call_basename` if found and `classname` is present in
///   `instantiated_classes`, or irep_idt() otherwise.
irep_idt ci_lazy_methodst::get_virtual_method_target(
  const std::unordered_set<irep_idt> &instantiated_classes,
  const irep_idt &call_basename,
  const irep_idt &classname,
  const symbol_tablet &symbol_table)
{
  // Program-wide, is this class ever instantiated?
  if(!instantiated_classes.count(classname))
    return irep_idt();

  resolve_inherited_componentt call_resolver(symbol_table, class_hierarchy);
  const resolve_inherited_componentt::inherited_componentt resolved_call =
    call_resolver(classname, call_basename, false);

  if(resolved_call.is_valid())
    return resolved_call.get_full_component_identifier();
  else
    return irep_idt();
}
