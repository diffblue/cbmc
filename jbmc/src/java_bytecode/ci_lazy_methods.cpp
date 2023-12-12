/*******************************************************************\

Module: Java Bytecode

Author: Diffblue Ltd.

\*******************************************************************/

#include "ci_lazy_methods.h"

#include <util/expr_iterator.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/suffix.h>
#include <util/symbol_table.h>

#include <goto-programs/resolve_inherited_component.h>

#include "java_bytecode_language.h"
#include "java_class_loader.h"
#include "java_entry_point.h"
#include "remove_exceptions.h"

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
/// \param synthetic_methods: map from synthetic method names to the type of
///   synthetic method (e.g. stub class static initialiser). Indicates that
///   these method bodies are produced internally, rather than generated from
///   Java bytecode.
ci_lazy_methodst::ci_lazy_methodst(
  const symbol_table_baset &symbol_table,
  const irep_idt &main_class,
  const std::vector<irep_idt> &main_jar_classes,
  const std::vector<load_extra_methodst> &lazy_methods_extra_entry_points,
  java_class_loadert &java_class_loader,
  const std::vector<irep_idt> &extra_instantiated_classes,
  const select_pointer_typet &pointer_type_selector,
  const synthetic_methods_mapt &synthetic_methods)
  : main_class(main_class),
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
  static const struct_tag_typet class_type("java::java.lang.Class");

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
/// \param message_handler: the message handler to use for output
/// \return Returns false on success
bool ci_lazy_methodst::operator()(
  symbol_table_baset &symbol_table,
  method_bytecodet &method_bytecode,
  const method_convertert &method_converter,
  message_handlert &message_handler)
{
  std::unordered_set<irep_idt> methods_to_convert_later =
    entry_point_methods(symbol_table, message_handler);

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
  std::unordered_set<class_method_descriptor_exprt, irep_hash>
    called_virtual_functions;
  bool class_initializer_seen = false;

  messaget log{message_handler};

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
            called_virtual_functions,
            message_handler);
          any_new_methods |= conversion_result.new_method_seen;
          class_initializer_seen |= conversion_result.class_initializer_seen;
        }
      }

      // Given the object types we now know may be created, populate more
      // possible virtual function call targets:

      log.debug() << "CI lazy methods: add virtual method targets ("
                  << called_virtual_functions.size() << " callsites)"
                  << messaget::eom;

      for(const class_method_descriptor_exprt &called_virtual_function :
          called_virtual_functions)
      {
        get_virtual_method_targets(
          called_virtual_function,
          instantiated_classes,
          methods_to_convert_later,
          symbol_table);
      }
    }

    any_new_classes = handle_virtual_methods_with_no_callees(
      methods_to_convert_later,
      instantiated_classes,
      called_virtual_functions,
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

  log.debug() << "CI lazy methods: removed "
              << symbol_table.symbols.size() - keep_symbols.symbols.size()
              << " unreachable methods and globals" << messaget::eom;

  auto sorted_to_keep = keep_symbols.sorted_symbol_names();
  auto all_sorted = symbol_table.sorted_symbol_names();
  auto it = sorted_to_keep.cbegin();
  for(const auto &id : all_sorted)
  {
    if(it == sorted_to_keep.cend() || id != *it)
      symbol_table.remove(id);
    else
      ++it;
  }

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
  const std::unordered_set<class_method_descriptor_exprt, irep_hash>
    &virtual_functions,
  symbol_table_baset &symbol_table)
{
  ci_lazy_methods_neededt lazy_methods_loader(
    methods_to_convert_later,
    instantiated_classes,
    symbol_table,
    pointer_type_selector);

  bool any_new_classes = false;
  for(const class_method_descriptor_exprt &virtual_function : virtual_functions)
  {
    std::unordered_set<irep_idt> candidate_target_methods;
    get_virtual_method_targets(
      virtual_function,
      instantiated_classes,
      candidate_target_methods,
      symbol_table);

    if(!candidate_target_methods.empty())
      continue;

    const java_method_typet &java_method_type =
      to_java_method_type(virtual_function.type());

    // Add the call class to instantiated_classes and assert that it
    // didn't already exist. It can't be instantiated already, otherwise it
    // would give a concrete definition of the called method, and
    // candidate_target_methods would be non-empty.
    const irep_idt &call_class = virtual_function.class_id();
    bool was_missing = instantiated_classes.count(call_class) == 0;
    CHECK_RETURN(was_missing);
    any_new_classes = true;

    const typet &this_type = java_method_type.get_this()->type();
    if(
      const pointer_typet *this_pointer_type =
        type_try_dynamic_cast<pointer_typet>(this_type))
    {
      lazy_methods_loader.add_all_needed_classes(*this_pointer_type);
    }

    // That should in particular have added call_class to the possibly
    // instantiated types.
    bool still_missing = instantiated_classes.count(call_class) == 0;
    CHECK_RETURN(!still_missing);

    // Make sure we add our return type as required, as we may not have
    // seen any concrete instances of it being created.
    const typet &return_type = java_method_type.return_type();
    if(
      const pointer_typet *return_pointer_type =
        type_try_dynamic_cast<pointer_typet>(return_type))
    {
      lazy_methods_loader.add_all_needed_classes(*return_pointer_type);
    }

    // Check that `get_virtual_method_target` returns a method now
    const irep_idt &method_name = virtual_function.mangled_method_name();
    const irep_idt method_id = get_virtual_method_target(
      instantiated_classes, method_name, call_class, symbol_table);
    CHECK_RETURN(!method_id.empty());

    // Add what it returns to methods_to_convert_later
    methods_to_convert_later.insert(method_id);
  }
  return any_new_classes;
}

/// Convert a method, add it to the populated set, add needed methods to
/// methods_to_convert_later and add virtual calls from the method to
/// virtual_functions
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
  symbol_table_baset &symbol_table,
  std::unordered_set<irep_idt> &methods_to_convert_later,
  std::unordered_set<irep_idt> &instantiated_classes,
  std::unordered_set<class_method_descriptor_exprt, irep_hash>
    &called_virtual_functions,
  message_handlert &message_handler)
{
  convert_method_resultt result;
  if(!methods_already_populated.insert(method_name).second)
    return result;

  messaget log{message_handler};
  log.debug() << "CI lazy methods: elaborate " << method_name << messaget::eom;

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
  gather_virtual_callsites(method_body, called_virtual_functions);

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
std::unordered_set<irep_idt> ci_lazy_methodst::entry_point_methods(
  const symbol_table_baset &symbol_table,
  message_handlert &message_handler)
{
  std::unordered_set<irep_idt> methods_to_convert_later;

  const main_function_resultt main_function =
    get_main_symbol(symbol_table, this->main_class, message_handler);
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
  std::unordered_set<class_method_descriptor_exprt, irep_hash> &result)
{
  if(e.id()!=ID_code)
    return;
  const codet &c=to_code(e);
  if(
    c.get_statement() == ID_function_call &&
    can_cast_expr<class_method_descriptor_exprt>(
      to_code_function_call(c).function()))
  {
    result.insert(
      to_class_method_descriptor_expr(to_code_function_call(c).function()));
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
  const class_method_descriptor_exprt &called_function,
  const std::unordered_set<irep_idt> &instantiated_classes,
  std::unordered_set<irep_idt> &callable_methods,
  symbol_table_baset &symbol_table)
{
  const auto &call_class = called_function.class_id();
  const auto &method_name = called_function.mangled_method_name();

  class_hierarchyt::idst self_and_child_classes =
    class_hierarchy.get_children_trans(call_class);
  self_and_child_classes.push_back(call_class);

  for(const irep_idt &class_name : self_and_child_classes)
  {
    const irep_idt method_id = get_virtual_method_target(
      instantiated_classes, method_name, class_name, symbol_table);
    if(!method_id.empty())
      callable_methods.insert(method_id);
  }
}

/// See output
/// \param e: expression tree to search
/// \param symbol_table: global symbol table
/// \param [out] needed: Populated with global variable symbols referenced from
///   `e` or its children.
void ci_lazy_methodst::gather_needed_globals(
  const exprt &e,
  const symbol_table_baset &symbol_table,
  symbol_table_baset &needed)
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
  {
    for(const auto &op : e.operands())
      gather_needed_globals(op, symbol_table, needed);
  }
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
  const symbol_table_baset &symbol_table)
{
  // Program-wide, is this class ever instantiated?
  if(!instantiated_classes.count(classname))
    return irep_idt();

  auto resolved_call =
    get_inherited_method_implementation(call_basename, classname, symbol_table);

  if(resolved_call)
    return resolved_call->get_full_component_identifier();
  else
    return irep_idt();
}
