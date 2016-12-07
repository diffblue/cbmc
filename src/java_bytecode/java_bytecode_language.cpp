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
#include "java_bytecode_instrument.h"
#include "java_bytecode_typecheck.h"
#include "java_entry_point.h"
#include "java_bytecode_parser.h"
#include "java_class_loader.h"
#include "java_utils.h"
#include <java_bytecode/ci_lazy_methods.h>

#include "expr2java.h"

/// Consume options that are java bytecode specific.
/// \param Command:line options
/// \return None
void java_bytecode_languaget::get_language_options(const cmdlinet &cmd)
{
  assume_inputs_non_null=cmd.isset("java-assume-inputs-non-null");
  string_refinement_enabled=cmd.isset("refine-strings");
  throw_runtime_exceptions=cmd.isset("java-throw-runtime-exceptions");
  if(cmd.isset("java-max-input-array-length"))
    max_nondet_array_length=
      std::stoi(cmd.get_value("java-max-input-array-length"));
  if(cmd.isset("java-max-input-tree-depth"))
    max_nondet_tree_depth=
      std::stoi(cmd.get_value("java-max-input-tree-depth"));
  if(cmd.isset("java-max-vla-length"))
    max_user_array_length=std::stoi(cmd.get_value("java-max-vla-length"));
  if(cmd.isset("lazy-methods-context-sensitive"))
    lazy_methods_mode=LAZY_METHODS_MODE_CONTEXT_SENSITIVE;
  else if(cmd.isset("lazy-methods"))
    lazy_methods_mode=LAZY_METHODS_MODE_CONTEXT_INSENSITIVE;
  else
    lazy_methods_mode=LAZY_METHODS_MODE_EAGER;

  const std::list<std::string> &extra_entry_points=
    cmd.get_values("lazy-methods-extra-entry-point");
  lazy_methods_extra_entry_points.insert(
    lazy_methods_extra_entry_points.end(),
    extra_entry_points.begin(),
    extra_entry_points.end());

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

/// Generate a _start function for a specific function.
/// \param entry_function_symbol: The symbol for the function that should be
///   used as the entry point
/// \param symbol_table: The symbol table for the program. The new _start
///   function symbol will be added to this table
/// \return Returns false if the _start method was generated correctly
bool java_bytecode_languaget::generate_start_function(
  const symbolt &entry_function_symbol,
  symbol_tablet &symbol_table)
{
  return generate_java_start_function(
    entry_function_symbol,
    symbol_table,
    get_message_handler(),
    assume_inputs_non_null,
    max_nondet_array_length,
    max_nondet_tree_depth,
    *pointer_type_selector);
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
    // build an object to potentially limit which classes are loaded
    java_class_loader_limitt class_loader_limit(
      get_message_handler(),
      java_cp_include_files);
    if(config.java.main_class.empty())
    {
      auto manifest=
        java_class_loader.jar_pool(class_loader_limit, path).get_manifest();
      std::string manifest_main_class=manifest["Main-Class"];

      // if the manifest declares a Main-Class line, we got a main class
      if(manifest_main_class!="")
        main_class=manifest_main_class;
    }
    else
      main_class=config.java.main_class;

    // do we have one now?
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
    UNREACHABLE;

  if(!main_class.empty())
  {
    status() << "Java main class: " << main_class << eom;
    java_class_loader(main_class);
  }

  return false;
}

bool java_bytecode_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  if(string_refinement_enabled)
    string_preprocess.initialize_conversion_table();

  // first generate a new struct symbol for each class and a new function symbol
  // for every method
  for(java_class_loadert::class_mapt::const_iterator
      c_it=java_class_loader.class_map.begin();
      c_it!=java_class_loader.class_map.end();
      c_it++)
  {
    if(c_it->second.parsed_class.name.empty())
      continue;

    if(java_bytecode_convert_class(
         c_it->second,
         symbol_table,
         get_message_handler(),
         max_user_array_length,
         lazy_methods,
         lazy_methods_mode,
         string_preprocess))
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
  else if(lazy_methods_mode==LAZY_METHODS_MODE_EAGER)
  {
    // Simply elaborate all methods symbols now.
    for(const auto &method_sig : lazy_methods)
    {
      java_bytecode_convert_method(
        *method_sig.second.first,
        *method_sig.second.second,
        symbol_table,
        get_message_handler(),
        max_user_array_length,
        string_preprocess);
    }
  }
  // Otherwise our caller is in charge of elaborating methods on demand.

  // now instrument runtime exceptions
  java_bytecode_instrument(
    symbol_table,
    throw_runtime_exceptions,
    get_message_handler());

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
  const auto method_converter=[&](
    const symbolt &symbol,
    const java_bytecode_parse_treet::methodt &method,
    ci_lazy_methods_neededt new_lazy_methods)
  {
    java_bytecode_convert_method(
      symbol,
      method,
      symbol_table,
      get_message_handler(),
      max_user_array_length,
      safe_pointer<ci_lazy_methods_neededt>::create_non_null(&new_lazy_methods),
      string_preprocess);
  };

  ci_lazy_methodst method_gather(
    symbol_table,
    main_class,
    main_jar_classes,
    lazy_methods_extra_entry_points,
    java_class_loader,
    get_pointer_type_selector(),
    get_message_handler());

  return method_gather(symbol_table, lazy_methods, method_converter);
}

const select_pointer_typet &
  java_bytecode_languaget::get_pointer_type_selector() const
{
  PRECONDITION(pointer_type_selector.get()!=nullptr);
  return *pointer_type_selector;
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
    string_preprocess);
}

/// Replace methods of the String library that are in the symbol table by code
/// generated by string_preprocess.
/// \param context: a symbol table
void java_bytecode_languaget::replace_string_methods(
  symbol_tablet &context)
{
  // Symbols that have code type are potentialy to be replaced
  std::list<symbolt> code_symbols;
  forall_symbols(symbol, context.symbols)
  {
    if(symbol->second.type.id()==ID_code)
      code_symbols.push_back(symbol->second);
  }

  for(const auto &symbol : code_symbols)
  {
    const irep_idt &id=symbol.name;
    exprt generated_code=string_preprocess.code_for_function(
      id, to_code_type(symbol.type), symbol.location, context);
    if(generated_code.is_not_nil())
    {
      // Replace body of the function by code generated by string preprocess
      symbolt &symbol=context.lookup(id);
      symbol.value=generated_code;
      // Specifically instrument the new code, since this comes after the
      // blanket instrumentation pass called before typechecking.
      java_bytecode_instrument_symbol(
        context,
        symbol,
        throw_runtime_exceptions,
        get_message_handler());
    }
  }
}

bool java_bytecode_languaget::final(symbol_tablet &symbol_table)
{
  java_internal_additions(symbol_table);

  // replace code of String methods calls by code we generate
  replace_string_methods(symbol_table);

  main_function_resultt res=
    get_main_symbol(symbol_table, main_class, get_message_handler());
  if(res.stop_convert)
    return res.error_found;

  // generate the test harness in __CPROVER__start and a call the entry point
  return
    java_entry_point(
      symbol_table,
      main_class,
      get_message_handler(),
      assume_inputs_non_null,
      max_nondet_array_length,
      max_nondet_tree_depth,
      get_pointer_type_selector());
}

void java_bytecode_languaget::show_parse(std::ostream &out)
{
  java_class_loader(main_class).output(out);
}

std::unique_ptr<languaget> new_java_bytecode_language()
{
  return util_make_unique<java_bytecode_languaget>();
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
