/*******************************************************************\

 Module: Java Bytecode

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/
#include "ci_lazy_methods.h"

#include <java_bytecode/java_entry_point.h>
#include <java_bytecode/java_class_loader.h>
#include <java_bytecode/java_utils.h>
#include <util/suffix.h>
#include <java_bytecode/java_string_library_preprocess.h>

#include <goto-programs/resolve_inherited_component.h>
#include <goto-programs/remove_exceptions.h>

/// Constructor for lazy-method loading
/// \param symbol_table: the symbol table to use
/// \param main_class: identifier of the entry point / main class
/// \param main_jar_classes: specify main class of jar if \p main_class is empty
/// \param lazy_methods_extra_entry_points: entry point functions to use
/// \param java_class_loader: the Java class loader to use
/// \param extra_needed_classes: list of class identifiers which are considered
/// to be required and therefore their methods should not be removed via
/// `lazy-methods`. Example of use: `ArrayList` as general implementation for
/// `List` interface.
/// \param pointer_type_selector: selector to handle correct pointer types
/// \param message_handler: the message handler to use for output
ci_lazy_methodst::ci_lazy_methodst(
  const symbol_tablet &symbol_table,
  const irep_idt &main_class,
  const std::vector<irep_idt> &main_jar_classes,
  const std::vector<irep_idt> &lazy_methods_extra_entry_points,
  java_class_loadert &java_class_loader,
  const std::vector<irep_idt> &extra_needed_classes,
  const select_pointer_typet &pointer_type_selector,
  message_handlert &message_handler,
  const synthetic_methods_mapt &synthetic_methods)
  : messaget(message_handler),
    main_class(main_class),
    main_jar_classes(main_jar_classes),
    lazy_methods_extra_entry_points(lazy_methods_extra_entry_points),
    java_class_loader(java_class_loader),
    extra_needed_classes(extra_needed_classes),
    pointer_type_selector(pointer_type_selector),
    synthetic_methods(synthetic_methods)
{
  // build the class hierarchy
  class_hierarchy(symbol_table);
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
  std::vector<irep_idt> method_worklist1;
  std::vector<irep_idt> method_worklist2;

  main_function_resultt main_function =
    get_main_symbol(symbol_table, main_class, get_message_handler());
  if(!main_function.is_success())
  {
    // Failed, mark all functions in the given main class(es)
    // reachable.
    std::vector<irep_idt> reachable_classes;
    if(!main_class.empty())
      reachable_classes.push_back(main_class);
    else
      reachable_classes = main_jar_classes;
    for(const auto &classname : reachable_classes)
    {
      const auto &methods=
        java_class_loader.class_map.at(classname).parsed_class.methods;
      for(const auto &method : methods)
      {
        const irep_idt methodid="java::"+id2string(classname)+"."+
          id2string(method.name)+":"+
          id2string(method.descriptor);
        method_worklist2.push_back(methodid);
      }
    }
  }
  else
    method_worklist2.push_back(main_function.main_function.name);

  // Add any extra entry points specified; we should elaborate these in the
  // same way as the main function.
  std::vector<irep_idt> extra_entry_points=lazy_methods_extra_entry_points;
  resolve_method_names(extra_entry_points, symbol_table);
  method_worklist2.insert(
    method_worklist2.begin(),
    extra_entry_points.begin(),
    extra_entry_points.end());

  std::set<irep_idt> needed_classes;

  {
    std::vector<irep_idt> initial_needed_methods;
    ci_lazy_methods_neededt initial_lazy_methods(
      initial_needed_methods,
      needed_classes,
      symbol_table);
    initialize_needed_classes(
      method_worklist2,
      namespacet(symbol_table),
      initial_lazy_methods);
    method_worklist2.insert(
      method_worklist2.end(),
      initial_needed_methods.begin(),
      initial_needed_methods.end());
  }

  std::set<irep_idt> methods_already_populated;
  std::vector<const code_function_callt *> virtual_callsites;

  bool any_new_methods=false;
  do
  {
    any_new_methods=false;
    while(!method_worklist2.empty())
    {
      std::swap(method_worklist1, method_worklist2);
      for(const auto &mname : method_worklist1)
      {
        if(!methods_already_populated.insert(mname).second)
          continue;
        debug() << "CI lazy methods: elaborate " << mname << eom;
        if(
          method_converter(
            mname,
            // Note this wraps *references* to method_worklist2 & needed_classes
            ci_lazy_methods_neededt(
              method_worklist2, needed_classes, symbol_table)))
        {
          // Couldn't convert this function
          continue;
        }
        gather_virtual_callsites(
          symbol_table.lookup_ref(mname).value,
          virtual_callsites);
        any_new_methods=true;
      }
      method_worklist1.clear();
    }

    // Given the object types we now know may be created, populate more
    // possible virtual function call targets:

    debug() << "CI lazy methods: add virtual method targets ("
            << virtual_callsites.size()
            << " callsites)"
            << eom;

    for(const auto &callsite : virtual_callsites)
    {
      // This will also create a stub if a virtual callsite has no targets.
      get_virtual_method_targets(
        *callsite,
        needed_classes,
        method_worklist2,
        symbol_table);
    }
  }
  while(any_new_methods);

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

/// Translates the given list of method names from human-readable to
/// internal syntax.
/// Expands any wildcards (entries ending in '.*') in the given method
/// list to include all non-static methods defined on the given class.
/// \param [in, out] methods: List of methods to expand. Any wildcard entries
///   will be deleted and the expanded entries appended to the end.
/// \param symbol_table: global symbol table
void ci_lazy_methodst::resolve_method_names(
  std::vector<irep_idt> &methods,
  const symbol_tablet &symbol_table)
{
  std::vector<irep_idt> new_methods;
  for(const irep_idt &method : methods)
  {
    const std::string &method_str=id2string(method);
    if(!has_suffix(method_str, ".*"))
    {
      std::string error_message;
      irep_idt internal_name=
        resolve_friendly_method_name(
          method_str,
          symbol_table,
          error_message);
      if(internal_name==irep_idt())
        throw "entry point "+error_message;
      new_methods.push_back(internal_name);
    }
    else
    {
      irep_idt classname="java::"+method_str.substr(0, method_str.length()-2);
      if(!symbol_table.has_symbol(classname))
        throw "wildcard entry point '"+method_str+"': unknown class";

      for(const auto &name_symbol : symbol_table.symbols)
      {
        if(name_symbol.second.type.id()!=ID_code)
          continue;
        if(!to_code_type(name_symbol.second.type).has_this())
          continue;
        if(has_prefix(id2string(name_symbol.first), id2string(classname)))
          new_methods.push_back(name_symbol.first);
      }
    }
  }

  methods=std::move(new_methods);
}

/// Build up a list of methods whose type may be passed around reachable
/// from the entry point.
/// \param entry_points: list of fully-qualified function names that
///   we should assume are reachable
/// \param ns: global namespace
/// \param [out] needed_lazy_methods: Populated with all Java reference types
///   whose references may be passed, directly or indirectly, to any of the
///   functions in `entry_points`.
void ci_lazy_methodst::initialize_needed_classes(
  const std::vector<irep_idt> &entry_points,
  const namespacet &ns,
  ci_lazy_methods_neededt &needed_lazy_methods)
{
  for(const auto &mname : entry_points)
  {
    const auto &symbol=ns.lookup(mname);
    const auto &mtype=to_code_type(symbol.type);
    for(const auto &param : mtype.parameters())
    {
      if(param.type().id()==ID_pointer)
      {
        const pointer_typet &original_pointer=to_pointer_type(param.type());
        initialize_all_needed_classes_from_pointer(
          original_pointer, ns, needed_lazy_methods);
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
  for(const auto &id : extra_needed_classes)
    needed_lazy_methods.add_needed_class("java::" + id2string(id));
}

/// Build up list of methods for types for a pointer and any types it
/// might be subsituted for. See
/// `initialize_needed_classes` for more details.
/// \param pointer_type: The type to gather methods for.
/// \param ns: global namespace
/// \param [out] needed_lazy_methods: Populated with all Java reference types
///   whose references may be passed, directly or indirectly, to any of the
///   functions in `entry_points`
void ci_lazy_methodst::initialize_all_needed_classes_from_pointer(
  const pointer_typet &pointer_type,
  const namespacet &ns,
  ci_lazy_methods_neededt &needed_lazy_methods)
{
  initialize_needed_classes_from_pointer(pointer_type, ns, needed_lazy_methods);

  const pointer_typet &subbed_pointer_type=
    pointer_type_selector.convert_pointer_type(pointer_type, ns);

  if(subbed_pointer_type!=pointer_type)
  {
    initialize_needed_classes_from_pointer(
      subbed_pointer_type, ns, needed_lazy_methods);
  }
}

/// Build up list of methods for types for a specific pointer type. See
/// `initialize_needed_classes` for more details.
/// \param pointer_type: The type to gather methods for.
/// \param ns: global namespace
/// \param [out] needed_lazy_methods: Populated with all Java reference types
///   whose references may be passed, directly or indirectly, to any of the
///   functions in `entry_points`
void ci_lazy_methodst::initialize_needed_classes_from_pointer(
  const pointer_typet &pointer_type,
  const namespacet &ns,
  ci_lazy_methods_neededt &needed_lazy_methods)
{
  const symbol_typet &class_type=to_symbol_type(pointer_type.subtype());
  const auto &param_classid=class_type.get_identifier();

  // Note here: different arrays may have different element types, so we should
  // explore again even if we've seen this classid before in the array case.
  if(needed_lazy_methods.add_needed_class(param_classid) ||
     is_java_array_tag(param_classid))
  {
    gather_field_types(pointer_type.subtype(), ns, needed_lazy_methods);
  }

  if(is_java_generic_type(pointer_type))
  {
    // Assume if this is a generic like X<A, B, C>, then any concrete parameters
    // will at some point be instantiated.
    const auto &generic_args =
      to_java_generic_type(pointer_type).generic_type_arguments();
    for(const auto &generic_arg : generic_args)
    {
      if(!is_java_generic_parameter(generic_arg))
      {
        initialize_needed_classes_from_pointer(
          generic_arg, ns, needed_lazy_methods);
      }
    }
  }
}

/// Get places where virtual functions are called.
/// \param e: expression tree to search
/// \param [out] result: filled with pointers to each function call within
///   e that calls a virtual function.
void ci_lazy_methodst::gather_virtual_callsites(
  const exprt &e,
  std::vector<const code_function_callt *> &result)
{
  if(e.id()!=ID_code)
    return;
  const codet &c=to_code(e);
  if(c.get_statement()==ID_function_call &&
     to_code_function_call(c).function().id()==ID_virtual_function)
  {
    result.push_back(&to_code_function_call(c));
  }
  else
  {
    for(const exprt &op : e.operands())
      gather_virtual_callsites(op, result);
  }
}

/// Find possible callees, excluding types that are not known to be
/// instantiated.
/// \param c: function call whose potential target functions should
///   be determined.
/// \param needed_classes: set of classes that can be instantiated. Any
///   potential callee not in this set will be ignored.
/// \param symbol_table: global symbol table
/// \param [out] needed_methods: Populated with all possible `c` callees, taking
///   `needed_classes` into account (virtual function overrides defined on
///   classes that are not 'needed' are ignored)
void ci_lazy_methodst::get_virtual_method_targets(
  const code_function_callt &c,
  const std::set<irep_idt> &needed_classes,
  std::vector<irep_idt> &needed_methods,
  symbol_tablet &symbol_table)
{
  const auto &called_function=c.function();
  PRECONDITION(called_function.id()==ID_virtual_function);

  const auto &call_class=called_function.get(ID_C_class);
  INVARIANT(
    !call_class.empty(), "All virtual calls should be aimed at a class");
  const auto &call_basename=called_function.get(ID_component_name);
  INVARIANT(
    !call_basename.empty(),
    "Virtual function must have a reasonable name after removing class");

  auto old_size=needed_methods.size();

  const irep_idt &self_method=
    get_virtual_method_target(
      needed_classes, call_basename, call_class, symbol_table);

  if(!self_method.empty())
  {
    needed_methods.push_back(self_method);
  }

  const auto child_classes=class_hierarchy.get_children_trans(call_class);
  for(const auto &child_class : child_classes)
  {
    const auto child_method=
      get_virtual_method_target(
        needed_classes,
        call_basename,
        child_class,
        symbol_table);
    if(!child_method.empty())
      needed_methods.push_back(child_method);
  }

  if(needed_methods.size()==old_size)
  {
    // Didn't find any candidate callee. Generate a stub.
    std::string stubname=id2string(call_class)+"."+id2string(call_basename);
    symbolt symbol;
    symbol.name=stubname;
    symbol.base_name=call_basename;
    symbol.type=c.function().type();
    symbol.value.make_nil();
    symbol.mode=ID_java;
    symbol_table.add(symbol);
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

/// See param needed_lazy_methods
/// \param class_type: root of class tree to search
/// \param ns: global namespace
/// \param [out] needed_lazy_methods: Popualted with all Java reference types
///   reachable starting at `class_type`. For example if `class_type` is
///   `symbol_typet("java::A")` and A has a B field, then `B` (but not `A`) will
///   noted as a needed class.
void ci_lazy_methodst::gather_field_types(
  const typet &class_type,
  const namespacet &ns,
  ci_lazy_methods_neededt &needed_lazy_methods)
{
  const auto &underlying_type=to_struct_type(ns.follow(class_type));
  if(is_java_array_tag(underlying_type.get_tag()))
  {
    // If class_type is not a symbol this may be a reference array,
    // but we can't tell what type.
    if(class_type.id() == ID_symbol)
    {
      const typet &element_type =
        java_array_element_type(to_symbol_type(class_type));
      if(element_type.id() == ID_pointer)
      {
        // This is a reference array -- mark its element type available.
        initialize_all_needed_classes_from_pointer(
          to_pointer_type(element_type), ns, needed_lazy_methods);
      }
    }
  }
  else
  {
    for(const auto &field : underlying_type.components())
    {
      if(field.type().id() == ID_struct || field.type().id() == ID_symbol)
        gather_field_types(field.type(), ns, needed_lazy_methods);
      else if(field.type().id() == ID_pointer)
      {
        if(field.type().subtype().id() == ID_symbol)
        {
          initialize_all_needed_classes_from_pointer(
            to_pointer_type(field.type()), ns, needed_lazy_methods);
        }
        else
        {
          // If raw structs were possible this would lead to missed
          // dependencies, as both array element and specialised generic type
          // information cannot be obtained in this case.
          // We should therefore only be skipping pointers such as the uint16t*
          // in our internal String representation.
          INVARIANT(
            field.type().subtype().id() != ID_struct,
            "struct types should be referred to by symbol at this stage");
        }
      }
    }
  }
}

/// Find a virtual callee, if one is defined and the callee type is known to
/// exist.
/// \param needed_classes: set of classes that can be instantiated.
///   Any potential callee not in this set will be ignored.
/// \param call_basename: unqualified function name with type signature (e.g.
///   "f:(I)")
/// \param classname: class name that may define or override a function named
///   `call_basename`.
/// \param symbol_table: global symtab
/// \return Returns the fully qualified name of `classname`'s definition of
///   `call_basename` if found and `classname` is present in `needed_classes`,
///   or irep_idt() otherwise.
irep_idt ci_lazy_methodst::get_virtual_method_target(
  const std::set<irep_idt> &needed_classes,
  const irep_idt &call_basename,
  const irep_idt &classname,
  const symbol_tablet &symbol_table)
{
  // Program-wide, is this class ever instantiated?
  if(!needed_classes.count(classname))
    return irep_idt();

  resolve_inherited_componentt call_resolver(symbol_table, class_hierarchy);
  const resolve_inherited_componentt::inherited_componentt resolved_call =
    call_resolver(classname, call_basename, false);

  if(resolved_call.is_valid())
    return resolved_call.get_full_component_identifier();
  else
    return irep_idt();
}
