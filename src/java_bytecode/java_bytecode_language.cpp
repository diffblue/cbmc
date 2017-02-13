/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_language.h"

#include <string>

#include <util/symbol_table.h>
#include <util/suffix.h>
#include <util/config.h>
#include <util/cmdline.h>
#include <util/string2int.h>
#include <util/invariant.h>
#include <json/json_parser.h>

#include <goto-programs/class_hierarchy.h>

#include "java_bytecode_convert_class.h"
#include "java_bytecode_convert_method.h"
#include "java_bytecode_internal_additions.h"
#include "java_bytecode_typecheck.h"
#include "java_entry_point.h"
#include "java_bytecode_parser.h"
#include "java_class_loader.h"

#include "expr2java.h"

/// Consume options that are java bytecode specific.
/// \param Command:line options
/// \return None
void java_bytecode_languaget::get_language_options(const cmdlinet &cmd)
{
  assume_inputs_non_null=cmd.isset("java-assume-inputs-non-null");
  string_refinement_enabled=cmd.isset("string-refine");
  if(cmd.isset("java-max-input-array-length"))
    max_nondet_array_length=
      std::stoi(cmd.get_value("java-max-input-array-length"));
  if(cmd.isset("java-max-vla-length"))
    max_user_array_length=std::stoi(cmd.get_value("java-max-vla-length"));
  if(cmd.isset("lazy-methods-context-sensitive"))
    lazy_methods_mode=LAZY_METHODS_MODE_CONTEXT_SENSITIVE;
  else if(cmd.isset("lazy-methods"))
    lazy_methods_mode=LAZY_METHODS_MODE_CONTEXT_INSENSITIVE;
  else
    lazy_methods_mode=LAZY_METHODS_MODE_EAGER;

  if(cmd.isset("java-cp-include-files"))
  {
    java_cp_include_files=cmd.get_value("java-cp-include-files");
    // load file list from JSON file
    if(java_cp_include_files[0]=='@')
    {
      jsont json_cp_config;
      if(parse_json(
           java_cp_include_files.substr(1),
           get_message_handler(),
           json_cp_config))
        throw "cannot read JSON input configuration for JAR loading";

      if(!json_cp_config.is_object())
        throw "the JSON file has a wrong format";
      jsont include_files=json_cp_config["jar"];
      if(!include_files.is_array())
         throw "the JSON file has a wrong format";

      // add jars from JSON config file to classpath
      for(const jsont &file_entry : include_files.array)
      {
        assert(file_entry.is_string() && has_suffix(file_entry.value, ".jar"));
        config.java.classpath.push_back(file_entry.value);
      }
    }
  }
  else
    java_cp_include_files=".*";

  language_options_initialized=true;
}

std::set<std::string> java_bytecode_languaget::extensions() const
{
  return { "class", "jar" };
}

void java_bytecode_languaget::modules_provided(std::set<std::string> &modules)
{
  // modules.insert(translation_unit(parse_path));
}

/// ANSI-C preprocessing
bool java_bytecode_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream)
{
  // there is no preprocessing!
  return true;
}

bool java_bytecode_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  PRECONDITION(language_options_initialized);
  java_class_loader.set_message_handler(get_message_handler());
  java_class_loader.set_java_cp_include_files(java_cp_include_files);

  // look at extension
  if(has_suffix(path, ".class"))
  {
    // override main_class
    main_class=java_class_loadert::file_to_class_name(path);
  }
  else if(has_suffix(path, ".jar"))
  {
    java_class_loader_limitt class_loader_limit(
      get_message_handler(),
      java_cp_include_files);
    if(config.java.main_class.empty())
    {
      // Does it have a main class set in the manifest?
      jar_filet::manifestt manifest=
        java_class_loader.jar_pool(class_loader_limit, path).get_manifest();
      std::string manifest_main_class=manifest["Main-Class"];

      if(manifest_main_class!="")
        main_class=manifest_main_class;
    }
    else
      main_class=config.java.main_class;

    // Do we have one now?
    if(main_class.empty())
    {
      status() << "JAR file without entry point: loading class files" << eom;
      java_class_loader.load_entire_jar(class_loader_limit, path);
      for(const auto &kv : java_class_loader.jar_map.at(path).entries)
        main_jar_classes.push_back(kv.first);
    }
    else
      java_class_loader.add_jar_file(path);
  }
  else
    assert(false);

  if(!main_class.empty())
  {
    status() << "Java main class: " << main_class << eom;
    java_class_loader(main_class);
  }

  return false;
}

/// Find a virtual callee, if one is defined and the callee type is known to
/// exist.
/// \par parameters: `needed_classes`: set of classes that can be instantiated.
///   Any potential callee not in this set will be ignored.
/// `call_basename`: unqualified function name with type signature (e.g.
///   "f:(I)")
/// `classname`: class name that may define or override a function named
///   `call_basename`.
/// `symbol_table`: global symtab
/// \return Returns the fully qualified name of `classname`'s definition of
///   `call_basename` if found and `classname` is present in `needed_classes`,
///   or irep_idt() otherwise.
static irep_idt get_virtual_method_target(
  const std::set<irep_idt> &needed_classes,
  const irep_idt &call_basename,
  const irep_idt &classname,
  const symbol_tablet &symbol_table)
{
  // Program-wide, is this class ever instantiated?
  if(!needed_classes.count(classname))
    return irep_idt();
  auto methodid=id2string(classname)+"."+id2string(call_basename);
  if(symbol_table.has_symbol(methodid))
    return methodid;
  else
    return irep_idt();
}

/// Find possible callees, excluding types that are not known to be
/// instantiated.
/// \par parameters: `c`: function call whose potential target functions should
///   be determined.
/// `needed_classes`: set of classes that can be instantiated. Any potential
///   callee not in this set will be ignored.
/// `symbol_table`: global symtab
/// `class_hierarchy`: global class hierarchy
/// \return Populates `needed_methods` with all possible `c` callees, taking
///   `needed_classes` into account (virtual function overrides defined on
///   classes that are not 'needed' are ignored)
static void get_virtual_method_targets(
  const code_function_callt &c,
  const std::set<irep_idt> &needed_classes,
  std::vector<irep_idt> &needed_methods,
  symbol_tablet &symbol_table,
  const class_hierarchyt &class_hierarchy)
{
  const auto &called_function=c.function();
  assert(called_function.id()==ID_virtual_function);

  const auto &call_class=called_function.get(ID_C_class);
  assert(!call_class.empty());
  const auto &call_basename=called_function.get(ID_component_name);
  assert(!call_basename.empty());

  auto old_size=needed_methods.size();

  auto child_classes=class_hierarchy.get_children_trans(call_class);
  for(const auto &child_class : child_classes)
  {
    auto child_method=
      get_virtual_method_target(
        needed_classes,
        call_basename,
        child_class,
        symbol_table);
    if(!child_method.empty())
      needed_methods.push_back(child_method);
  }

  irep_idt parent_class_id=call_class;
  while(1)
  {
    auto parent_method=
      get_virtual_method_target(
        needed_classes,
        call_basename,
        parent_class_id,
        symbol_table);
    if(!parent_method.empty())
    {
      needed_methods.push_back(parent_method);
      break;
    }
    else
    {
      auto findit=class_hierarchy.class_map.find(parent_class_id);
      if(findit==class_hierarchy.class_map.end())
        break;
      else
      {
        const auto &entry=findit->second;
        if(entry.parents.empty())
          break;
        else
          parent_class_id=entry.parents[0];
      }
    }
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
/// \par parameters: `e`: expression tree to search
/// \return Populates `result` with pointers to each function call within e that
///   calls a virtual function.
static void gather_virtual_callsites(
  const exprt &e,
  std::vector<const code_function_callt *> &result)
{
  if(e.id()!=ID_code)
    return;
  const codet &c=to_code(e);
  if(c.get_statement()==ID_function_call &&
     to_code_function_call(c).function().id()==ID_virtual_function)
    result.push_back(&to_code_function_call(c));
  else
    forall_operands(it, e)
      gather_virtual_callsites(*it, result);
}

/// See output
/// \par parameters: `e`: expression tree to search
/// `symbol_table`: global symtab
/// \return Populates `needed` with global variable symbols referenced from `e`
///   or its children.
static void gather_needed_globals(
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
    auto findit=symbol_table.symbols.find(to_symbol_expr(e).get_identifier());
    if(findit!=symbol_table.symbols.end() &&
       findit->second.is_static_lifetime)
    {
      needed.add(findit->second);
    }
  }
  else
    forall_operands(opit, e)
      gather_needed_globals(*opit, symbol_table, needed);
}

/// See output
/// \par parameters: `class_type`: root of class tree to search
/// `ns`: global namespace
/// \return Populates `lazy_methods` with all Java reference types reachable
///   starting at `class_type`. For example if `class_type` is
///   `symbol_typet("java::A")` and A has a B field, then `B` (but not `A`) will
///   noted as a needed class.
static void gather_field_types(
  const typet &class_type,
  const namespacet &ns,
  ci_lazy_methodst &lazy_methods)
{
  const auto &underlying_type=to_struct_type(ns.follow(class_type));
  for(const auto &field : underlying_type.components())
  {
    if(field.type().id()==ID_struct || field.type().id()==ID_symbol)
      gather_field_types(field.type(), ns, lazy_methods);
    else if(field.type().id()==ID_pointer)
    {
      // Skip array primitive pointers, for example:
      if(field.type().subtype().id()!=ID_symbol)
        continue;
      const auto &field_classid=
        to_symbol_type(field.type().subtype()).get_identifier();
      if(lazy_methods.add_needed_class(field_classid))
        gather_field_types(field.type().subtype(), ns, lazy_methods);
    }
  }
}

/// See output
/// \par parameters: `entry_points`: list of fully-qualified function names that
///   we should assume are reachable
/// `ns`: global namespace
/// `ch`: global class hierarchy
/// \return Populates `lazy_methods` with all Java reference types whose
///   references may be passed, directly or indirectly, to any of the functions
///   in `entry_points`.
static void initialize_needed_classes(
  const std::vector<irep_idt> &entry_points,
  const namespacet &ns,
  const class_hierarchyt &ch,
  ci_lazy_methodst &lazy_methods)
{
  for(const auto &mname : entry_points)
  {
    const auto &symbol=ns.lookup(mname);
    const auto &mtype=to_code_type(symbol.type);
    for(const auto &param : mtype.parameters())
    {
      if(param.type().id()==ID_pointer)
      {
        const auto &param_classid=
          to_symbol_type(param.type().subtype()).get_identifier();
        std::vector<irep_idt> class_and_parents=
          ch.get_parents_trans(param_classid);
        class_and_parents.push_back(param_classid);
        for(const auto &classid : class_and_parents)
          lazy_methods.add_needed_class(classid);
        gather_field_types(param.type().subtype(), ns, lazy_methods);
      }
    }
  }

  // Also add classes whose instances are magically
  // created by the JVM and so won't be spotted by
  // looking for constructors and calls as usual:
  lazy_methods.add_needed_class("java::java.lang.String");
  lazy_methods.add_needed_class("java::java.lang.Class");
  lazy_methods.add_needed_class("java::java.lang.Object");
}

bool java_bytecode_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  if(string_refinement_enabled)
    character_preprocess.initialize_conversion_table();

  // first convert all
  for(java_class_loadert::class_mapt::const_iterator
      c_it=java_class_loader.class_map.begin();
      c_it!=java_class_loader.class_map.end();
      c_it++)
  {
    if(c_it->second.parsed_class.name.empty())
      continue;

    debug() << "Converting class " << c_it->first << eom;

    if(java_bytecode_convert_class(
         c_it->second,
         symbol_table,
         get_message_handler(),
         max_user_array_length,
         lazy_methods,
         lazy_methods_mode,
         string_refinement_enabled,
         character_preprocess))
      return true;
  }

  // Now incrementally elaborate methods
  // that are reachable from this entry point.
  if(lazy_methods_mode==LAZY_METHODS_MODE_CONTEXT_INSENSITIVE)
  {
    // ci: context-insensitive.
    if(do_ci_lazy_method_conversion(symbol_table, lazy_methods))
      return true;
  }

  // Now incrementally elaborate methods
  // that are reachable from this entry point.
  if(lazy_methods_mode==LAZY_METHODS_MODE_CONTEXT_INSENSITIVE)
  {
    if(do_ci_lazy_method_conversion(symbol_table, lazy_methods))
      return true;
  }

  // now typecheck all
  if(java_bytecode_typecheck(
       symbol_table, get_message_handler()))
    return true;

  class_hierarchyt ch;
  ch(symbol_table);

  std::vector<irep_idt> method_worklist1;
  std::vector<irep_idt> method_worklist2;

  auto main_function=
    get_main_symbol(symbol_table, main_class, get_message_handler(), true);
  if(main_function.stop_convert)
  {
    // Failed, mark all functions in the given main class(es) reachable.
    std::vector<irep_idt> reachable_classes;
    if(!main_class.empty())
      reachable_classes.push_back(main_class);
    else
      reachable_classes=main_jar_classes;
    for(const auto &classname : reachable_classes)
    {
      const auto &methods=
        java_class_loader.class_map.at(classname).parsed_class.methods;
      for(const auto &method : methods)
      {
        const irep_idt methodid="java::"+id2string(classname)+"."+
          id2string(method.name)+":"+
          id2string(method.signature);
        method_worklist2.push_back(methodid);
      }
    }
  }
  else
    method_worklist2.push_back(main_function.main_function.name);

  std::set<irep_idt> needed_classes;
  initialize_needed_classes(
    method_worklist2,
    namespacet(symbol_table),
    ch,
    needed_classes);

  std::set<irep_idt> methods_already_populated;
  std::vector<const code_function_callt*> virtual_callsites;

  bool any_new_methods;
  do
  {
    any_new_methods=false;
    while(method_worklist2.size()!=0)
    {
      std::swap(method_worklist1, method_worklist2);
      for(const auto &mname : method_worklist1)
      {
        if(!methods_already_populated.insert(mname).second)
          continue;
        auto findit=lazy_methods.find(mname);
        if(findit==lazy_methods.end())
        {
          debug() << "Skip " << mname << eom;
          continue;
        }
        debug() << "CI lazy methods: elaborate " << mname << eom;
        const auto &parsed_method=findit->second;
        java_bytecode_convert_method(
          *parsed_method.first,
          *parsed_method.second,
          symbol_table,
          get_message_handler(),
          disable_runtime_checks,
          max_user_array_length,
          &method_worklist2,
          &needed_classes);
        gather_virtual_callsites(
          symbol_table.lookup(mname).value,
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
      get_virtual_method_targets(*callsite, needed_classes, method_worklist2,
				 symbol_table, ch);
    }

  } while(any_new_methods);

  // Remove symbols for methods that were declared but never used:
  symbol_tablet keep_symbols;

  for(const auto &sym : symbol_table.symbols)
  {
    if(sym.second.is_static_lifetime)
      continue;
    if(lazy_methods.count(sym.first) &&
       !methods_already_populated.count(sym.first))
    {
      continue;
    }
    if(sym.second.type.id()==ID_code)
      gather_needed_globals(sym.second.value, symbol_table, keep_symbols);
    keep_symbols.add(sym.second);
  }

  debug() << "CI lazy methods: removed "
          << symbol_table.symbols.size() - keep_symbols.symbols.size()
          << " unreachable methods and globals"
          << eom;

  symbol_table.swap(keep_symbols);

  // now typecheck all
  if(java_bytecode_typecheck(
       symbol_table, get_message_handler(), string_refinement_enabled))
    return true;

  return false;
}

/// Uses a simple context-insensitive ('ci') analysis to determine which methods
/// may be reachable from the main entry point. In brief, static methods are
/// reachable if we find a callsite in another reachable site, while virtual
/// methods are reachable if we find a virtual callsite targeting a compatible
/// type *and* a constructor callsite indicating an object of that type may be
/// instantiated (or evidence that an object of that type exists before the main
/// function is entered, such as being passed as a parameter).
/// \par parameters: `symbol_table`: global symbol table
/// `lazy_methods`: map from method names to relevant symbol and parsed-method
///   objects.
/// \return Elaborates lazily-converted methods that may be reachable starting
///   from the main entry point (usually provided with the --function command-
///   line option) (side-effect on the symbol_table). Returns false on success.
bool java_bytecode_languaget::do_ci_lazy_method_conversion(
  symbol_tablet &symbol_table,
  lazy_methodst &lazy_methods)
{
  class_hierarchyt ch;
  ch(symbol_table);

  std::vector<irep_idt> method_worklist1;
  std::vector<irep_idt> method_worklist2;

  auto main_function=
    get_main_symbol(symbol_table, main_class, get_message_handler(), true);
  if(main_function.stop_convert)
  {
    // Failed, mark all functions in the given main class(es) reachable.
    std::vector<irep_idt> reachable_classes;
    if(!main_class.empty())
      reachable_classes.push_back(main_class);
    else
      reachable_classes=main_jar_classes;
    for(const auto &classname : reachable_classes)
    {
      const auto &methods=
        java_class_loader.class_map.at(classname).parsed_class.methods;
      for(const auto &method : methods)
      {
        const irep_idt methodid="java::"+id2string(classname)+"."+
          id2string(method.name)+":"+
          id2string(method.signature);
        method_worklist2.push_back(methodid);
      }
    }
  }
  else
    method_worklist2.push_back(main_function.main_function.name);

  std::set<irep_idt> needed_classes;

  {
    std::vector<irep_idt> needed_clinits;
    ci_lazy_methodst initial_lazy_methods(
      needed_clinits,
      needed_classes,
      symbol_table);
    initialize_needed_classes(
      method_worklist2,
      namespacet(symbol_table),
      ch,
      initial_lazy_methods);
    method_worklist2.insert(
      method_worklist2.end(),
      needed_clinits.begin(),
      needed_clinits.end());
  }

  std::set<irep_idt> methods_already_populated;
  std::vector<const code_function_callt *> virtual_callsites;

  bool any_new_methods;
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
        auto findit=lazy_methods.find(mname);
        if(findit==lazy_methods.end())
        {
          debug() << "Skip " << mname << eom;
          continue;
        }
        debug() << "CI lazy methods: elaborate " << mname << eom;
        const auto &parsed_method=findit->second;
        // Note this wraps *references* to method_worklist2, needed_classes:
        ci_lazy_methodst lazy_methods(
          method_worklist2,
          needed_classes,
          symbol_table);
        java_bytecode_convert_method(
          *parsed_method.first,
          *parsed_method.second,
          symbol_table,
          get_message_handler(),
          max_user_array_length,
          safe_pointer<ci_lazy_methodst>::create_non_null(&lazy_methods),
          character_preprocess);
        gather_virtual_callsites(
          symbol_table.lookup(mname).value,
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
        symbol_table,
        ch);
    }
  }
  while(any_new_methods);

  // Remove symbols for methods that were declared but never used:
  symbol_tablet keep_symbols;

  for(const auto &sym : symbol_table.symbols)
  {
    if(sym.second.is_static_lifetime)
      continue;
    if(lazy_methods.count(sym.first) &&
       !methods_already_populated.count(sym.first))
    {
      continue;
    }
    if(sym.second.type.id()==ID_code)
      gather_needed_globals(sym.second.value, symbol_table, keep_symbols);
    keep_symbols.add(sym.second);
  }

  debug() << "CI lazy methods: removed "
          << symbol_table.symbols.size() - keep_symbols.symbols.size()
          << " unreachable methods and globals"
          << eom;

  symbol_table.swap(keep_symbols);

  return false;
}

/// Provide feedback to `language_filest` so that when asked for a lazy method,
/// it can delegate to this instance of java_bytecode_languaget.
/// \return Populates `methods` with the complete list of lazy methods that are
///   available to convert (those which are valid parameters for
///   `convert_lazy_method`)
void java_bytecode_languaget::lazy_methods_provided(
  std::set<irep_idt> &methods) const
{
  for(const auto &kv : lazy_methods)
    methods.insert(kv.first);
}

/// Promote a lazy-converted method (one whose type is known but whose body
/// hasn't been converted) into a fully- elaborated one.
/// \par parameters: `id`: method ID to convert
/// `symtab`: global symbol table
/// \return Amends the symbol table entry for function `id`, which should be a
///   lazy method provided by this instance of `java_bytecode_languaget`. It
///   should initially have a nil value. After this method completes, it will
///   have a value representing the method body, identical to that produced
///   using eager method conversion.
void java_bytecode_languaget::convert_lazy_method(
  const irep_idt &id,
  symbol_tablet &symtab)
{
  const auto &lazy_method_entry=lazy_methods.at(id);
  java_bytecode_convert_method(
    *lazy_method_entry.first,
    *lazy_method_entry.second,
    symtab,
    get_message_handler(),
    max_user_array_length,
    character_preprocess);
}

bool java_bytecode_languaget::final(symbol_tablet &symbol_table)
{
  /*
  if(c_final(symbol_table, message_handler)) return true;
  */
  java_internal_additions(symbol_table);


  main_function_resultt res=
    get_main_symbol(symbol_table, main_class, get_message_handler());
  if(res.stop_convert)
    return res.error_found;

  symbolt entry=res.main_function;

  return(
    java_entry_point(
      symbol_table,
      main_class,
      get_message_handler(),
      assume_inputs_non_null,
      max_nondet_array_length));
}

void java_bytecode_languaget::show_parse(std::ostream &out)
{
  java_class_loader(main_class).output(out);
}

languaget *new_java_bytecode_language()
{
  return new java_bytecode_languaget;
}

bool java_bytecode_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2java(expr, ns);
  return false;
}

bool java_bytecode_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2java(type, ns);
  return false;
}

bool java_bytecode_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  const namespacet &ns)
{
  #if 0
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(code);

  // parsing

  java_bytecode_parser.clear();
  java_bytecode_parser.filename="";
  java_bytecode_parser.in=&i_preprocessed;
  java_bytecode_parser.set_message_handler(message_handler);
  java_bytecode_parser.grammar=java_bytecode_parsert::EXPRESSION;
  java_bytecode_parser.mode=java_bytecode_parsert::GCC;
  java_bytecode_scanner_init();

  bool result=java_bytecode_parser.parse();

  if(java_bytecode_parser.parse_tree.items.empty())
    result=true;
  else
  {
    expr=java_bytecode_parser.parse_tree.items.front().value();

    result=java_bytecode_convert(expr, "", message_handler);

    // typecheck it
    if(!result)
      result=java_bytecode_typecheck(expr, message_handler, ns);
  }

  // save some memory
  java_bytecode_parser.clear();

  return result;
  #endif

  return true; // fail for now
}

java_bytecode_languaget::~java_bytecode_languaget()
{
}
