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
#include <util/expr_iterator.h>
#include <util/journalling_symbol_table.h>
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
#include "java_string_literals.h"
#include "java_utils.h"
#include <java_bytecode/ci_lazy_methods.h>
#include <java_bytecode/generate_java_generic_type.h>

#include "expr2java.h"

/// Consume options that are java bytecode specific.
/// \param Command:line options
/// \return None
void java_bytecode_languaget::get_language_options(const cmdlinet &cmd)
{
  assume_inputs_non_null=cmd.isset("java-assume-inputs-non-null");
  java_class_loader.use_core_models=!cmd.isset("no-core-models");
  string_refinement_enabled=cmd.isset("refine-strings");
  throw_runtime_exceptions=cmd.isset("java-throw-runtime-exceptions");
  if(cmd.isset("java-max-input-array-length"))
    object_factory_parameters.max_nondet_array_length=
      std::stoi(cmd.get_value("java-max-input-array-length"));
  if(cmd.isset("java-max-input-tree-depth"))
    object_factory_parameters.max_nondet_tree_depth=
      std::stoi(cmd.get_value("java-max-input-tree-depth"));
  if(cmd.isset("string-max-input-length"))
    object_factory_parameters.max_nondet_string_length=
      std::stoi(cmd.get_value("string-max-input-length"));
  object_factory_parameters.string_printable = cmd.isset("string-printable");
  if(cmd.isset("java-max-vla-length"))
    max_user_array_length=std::stoi(cmd.get_value("java-max-vla-length"));
  if(cmd.isset("lazy-methods-context-sensitive"))
    lazy_methods_mode=LAZY_METHODS_MODE_CONTEXT_SENSITIVE;
  else if(cmd.isset("lazy-methods"))
    lazy_methods_mode=LAZY_METHODS_MODE_CONTEXT_INSENSITIVE;
  else
    lazy_methods_mode=LAZY_METHODS_MODE_EAGER;

  if(cmd.isset("java-throw-runtime-exceptions"))
  {
    throw_runtime_exceptions = true;
    java_load_classes.insert(
        java_load_classes.end(),
        exception_needed_classes.begin(),
        exception_needed_classes.end());
  }
  if(cmd.isset("java-load-class"))
  {
    const auto &values = cmd.get_values("java-load-class");
    java_load_classes.insert(
        java_load_classes.end(), values.begin(), values.end());
  }

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
  java_class_loader.add_load_classes(java_load_classes);
  if(string_refinement_enabled)
  {
    string_preprocess.initialize_known_type_table();

    auto get_string_base_classes = [this](const irep_idt &id) { // NOLINT (*)
      return string_preprocess.get_string_type_base_classes(id);
    };

    java_class_loader.set_extra_class_refs_function(get_string_base_classes);
  }

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

/// Infer fields that must exist on opaque types from field accesses against
/// them. Note that we don't yet try to infer inheritence between opaque types
/// here, so we may introduce the same field onto a type and its ancestor
/// without realising that is in fact the same field, inherited from that
/// ancestor. This can lead to incorrect results when opaque types are cast
/// to other opaque types and their fields do not alias as intended.
/// \param parse_tree: class parse tree
/// \param symbol_table: global symbol table
static void infer_opaque_type_fields(
  const java_bytecode_parse_treet &parse_tree,
  symbol_tablet &symbol_table)
{
  namespacet ns(symbol_table);
  for(const auto &method : parse_tree.parsed_class.methods)
  {
    for(const auto &instruction : method.instructions)
    {
      if(instruction.statement == "getfield" ||
         instruction.statement == "putfield")
      {
        const exprt &fieldref = instruction.args[0];
        const symbolt *class_symbol =
          symbol_table.lookup(fieldref.get(ID_class));
        INVARIANT(
          class_symbol != nullptr, "all field types should have been loaded");

        const class_typet *class_type = &to_class_type(class_symbol->type);
        irep_idt class_symbol_id = fieldref.get(ID_class);
        const irep_idt &component_name = fieldref.get(ID_component_name);
        while(!class_type->has_component(component_name))
        {
          if(class_type->get_bool(ID_incomplete_class))
          {
            // Accessing a field of an incomplete (opaque) type.
            symbolt &writable_class_symbol =
              symbol_table.get_writeable_ref(class_symbol_id);
            auto &add_to_components =
              to_struct_type(writable_class_symbol.type).components();
            add_to_components.push_back(
              struct_typet::componentt(component_name, fieldref.type()));
            add_to_components.back().set_base_name(component_name);
            add_to_components.back().set_pretty_name(component_name);
            break;
          }
          else
          {
            // Not present here: check the superclass.
            INVARIANT(
              class_type->bases().size() != 0,
              "class missing an expected field should have a superclass");
            const symbol_typet &superclass_type =
              to_symbol_type(class_type->bases()[0].type());
            class_symbol_id = superclass_type.get_identifier();
            class_type = &to_class_type(ns.follow(superclass_type));
          }
        }
      }
    }
  }
}

/// Create if necessary, then return the constant global java.lang.Class symbol
/// for a given class id
/// \param class_id: class identifier
/// \param symbol_table: global symbol table; a symbol may be added
/// \return java.lang.Class typed symbol expression
static symbol_exprt get_or_create_class_literal_symbol(
  const irep_idt &class_id, symbol_tablet &symbol_table)
{
  symbol_typet java_lang_Class("java::java.lang.Class");
  symbol_exprt symbol_expr(
    id2string(class_id)+"@class_model",
    java_lang_Class);
  if(!symbol_table.has_symbol(symbol_expr.get_identifier()))
  {
    symbolt new_class_symbol;
    new_class_symbol.name = symbol_expr.get_identifier();
    new_class_symbol.type = symbol_expr.type();
    INVARIANT(
      has_prefix(id2string(new_class_symbol.name), "java::"),
      "class identifier should have 'java::' prefix");
    new_class_symbol.base_name =
      id2string(new_class_symbol.name).substr(6);
    new_class_symbol.mode = ID_java;
    new_class_symbol.is_lvalue = true;
    new_class_symbol.is_state_var = true;
    new_class_symbol.is_static_lifetime = true;
    symbol_table.add(new_class_symbol);
  }

  return symbol_expr;
}

/// Get result of a Java load-constant (ldc) instruction.
/// Possible cases:
/// 1) Pushing a String causes a reference to a java.lang.String object
/// to be constructed and pushed onto the operand stack.
/// 2) Pushing an int or a float causes a primitive value to be pushed
/// onto the stack.
/// 3) Pushing a Class constant causes a reference to a java.lang.Class
/// to be pushed onto the operand stack
/// \param ldc_arg0: raw operand to the ldc opcode
/// \param symbol_table: global symbol table. If the argument `ldc_arg0` is a
///   String or Class constant then a new constant global may be added.
/// \param string_refinement_enabled: true if --refine-strings is enabled, which
///   influences how String literals are structured.
/// \return ldc result
static exprt get_ldc_result(
  const exprt &ldc_arg0,
  symbol_tablet &symbol_table,
  bool string_refinement_enabled)
{
  if(ldc_arg0.id() == ID_type)
  {
    const irep_idt &class_id = ldc_arg0.type().get(ID_identifier);
    return
      address_of_exprt(
        get_or_create_class_literal_symbol(class_id, symbol_table));
  }
  else if(ldc_arg0.id() == ID_java_string_literal)
  {
    return
      address_of_exprt(
        get_or_create_string_literal_symbol(
          ldc_arg0, symbol_table, string_refinement_enabled));
  }
  else
  {
    INVARIANT(
      ldc_arg0.id() == ID_constant,
      "ldc argument should be constant, string literal or class literal");
    return ldc_arg0;
  }
}

/// Creates global variables for constants mentioned in a given method. These
/// are either string literals, or class literals (the java.lang.Class instance
/// returned by `(some_reference_typed_expression).class`). The method parse
/// tree is rewritten to directly reference these globals.
/// \param parse_tree: parse tree to search for constant global references
/// \param symbol_table: global symbol table, to which constant globals will be
///   added.
/// \param string_refinement_enabled: true if `--refine-stings` is active,
///   which changes how string literals are structured.
static void generate_constant_global_variables(
  java_bytecode_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  bool string_refinement_enabled)
{
  for(auto &method : parse_tree.parsed_class.methods)
  {
    for(auto &instruction : method.instructions)
    {
      // ldc* instructions are Java bytecode "load constant" ops, which can
      // retrieve a numeric constant, String literal, or Class literal.
      if(instruction.statement == "ldc" ||
         instruction.statement == "ldc2" ||
         instruction.statement == "ldc_w" ||
         instruction.statement == "ldc2_w")
      {
        INVARIANT(
          instruction.args.size() != 0,
          "ldc instructions should have an argument");
        instruction.args[0] =
          get_ldc_result(
            instruction.args[0],
            symbol_table,
            string_refinement_enabled);
      }
    }
  }
}

bool java_bytecode_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  PRECONDITION(language_options_initialized);

  java_internal_additions(symbol_table);

  if(string_refinement_enabled)
    string_preprocess.initialize_conversion_table();

  // Must load java.lang.Object first to avoid stubbing
  // This ordering could alternatively be enforced by
  // moving the code below to the class loader.
  java_class_loadert::class_mapt::const_iterator it=
    java_class_loader.class_map.find("java.lang.Object");
  if(it!=java_class_loader.class_map.end())
  {
    if(java_bytecode_convert_class(
     it->second,
     symbol_table,
     get_message_handler(),
     max_user_array_length,
     method_bytecode,
     lazy_methods_mode,
     string_preprocess))
       return true;
  }

  // first generate a new struct symbol for each class and a new function symbol
  // for every method
  for(java_class_loadert::class_mapt::const_iterator
      c_it=java_class_loader.class_map.begin();
      c_it!=java_class_loader.class_map.end();
      c_it++)
  {
    if(c_it->second.parsed_class.name.empty())
      continue;

    if(
      java_bytecode_convert_class(
        c_it->second,
        symbol_table,
        get_message_handler(),
        max_user_array_length,
        method_bytecode,
        lazy_methods_mode,
        string_preprocess))
      return true;
  }

  // find and mark all implicitly generic class types
  // this can only be done once all the class symbols have been created
  for(const auto &c : java_class_loader.class_map)
  {
    if(c.second.parsed_class.name.empty())
      continue;
    try
    {
      mark_java_implicitly_generic_class_type(
        c.second.parsed_class.name, symbol_table);
    }
    catch(missing_outer_class_symbol_exceptiont &)
    {
      messaget::warning()
        << "Not marking class " << c.first
        << " implicitly generic due to missing outer class symbols"
        << messaget::eom;
    }
  }

  // Infer fields on opaque types based on the method instructions just loaded.
  // For example, if we don't have bytecode for field x of class A, but we can
  // see an int-typed getfield instruction referring to it, add that field now.
  for(const auto &c : java_class_loader.class_map)
  {
    infer_opaque_type_fields(c.second, symbol_table);
  }

  // Create global variables for constants (String and Class literals) up front.
  // This means that when running with lazy loading, we will be aware of these
  // literal globals' existence when __CPROVER_initialize is generated in
  // `generate_support_functions`.
  const std::size_t before_constant_globals_size = symbol_table.symbols.size();
  for(auto &c : java_class_loader.class_map)
  {
    generate_constant_global_variables(
      c.second,
      symbol_table,
      string_refinement_enabled);
  }
  status() << "Java: added "
           << (symbol_table.symbols.size() - before_constant_globals_size)
           << " String or Class constant symbols"
           << messaget::eom;

  // Now incrementally elaborate methods
  // that are reachable from this entry point.
  if(lazy_methods_mode==LAZY_METHODS_MODE_CONTEXT_INSENSITIVE)
  {
    // ci: context-insensitive.
    if(do_ci_lazy_method_conversion(symbol_table, method_bytecode))
      return true;
  }
  else if(lazy_methods_mode==LAZY_METHODS_MODE_EAGER)
  {
    journalling_symbol_tablet journalling_symbol_table =
      journalling_symbol_tablet::wrap(symbol_table);
    // Convert all methods for which we have bytecode now
    for(const auto &method_sig : method_bytecode)
    {
      convert_single_method(method_sig.first, journalling_symbol_table);
    }
    // Now convert all newly added string methods
    for(const auto &fn_name : journalling_symbol_table.get_inserted())
    {
      if(string_preprocess.implements_function(fn_name))
        convert_single_method(fn_name, symbol_table);
    }
  }
  // Otherwise our caller is in charge of elaborating methods on demand.

  // now instrument runtime exceptions
  java_bytecode_instrument(
    symbol_table,
    throw_runtime_exceptions,
    get_message_handler());

  // now typecheck all
  return java_bytecode_typecheck(
    symbol_table, get_message_handler(), string_refinement_enabled);
}

bool java_bytecode_languaget::generate_support_functions(
  symbol_tablet &symbol_table)
{
  PRECONDITION(language_options_initialized);

  main_function_resultt res=
    get_main_symbol(symbol_table, main_class, get_message_handler());
  if(!res.is_success())
    return res.is_error();

  // Load the main function into the symbol table to get access to its
  // parameter names
  convert_lazy_method(res.main_function.name, symbol_table);

  // generate the test harness in __CPROVER__start and a call the entry point
  return
    java_entry_point(
      symbol_table,
      main_class,
      get_message_handler(),
      assume_inputs_non_null,
      object_factory_parameters,
      get_pointer_type_selector());
}

/// Uses a simple context-insensitive ('ci') analysis to determine which methods
/// may be reachable from the main entry point. In brief, static methods are
/// reachable if we find a callsite in another reachable site, while virtual
/// methods are reachable if we find a virtual callsite targeting a compatible
/// type *and* a constructor callsite indicating an object of that type may be
/// instantiated (or evidence that an object of that type exists before the main
/// function is entered, such as being passed as a parameter).
/// \par parameters: `symbol_table`: global symbol table
/// `method_bytecode`: map from method names to relevant symbol and
///   parsed-method objects.
/// \return Elaborates lazily-converted methods that may be reachable starting
///   from the main entry point (usually provided with the --function command-
///   line option) (side-effect on the symbol_table). Returns false on success.
bool java_bytecode_languaget::do_ci_lazy_method_conversion(
  symbol_tablet &symbol_table,
  method_bytecodet &method_bytecode)
{
  const method_convertert method_converter =
    [this, &symbol_table]
      (const irep_idt &function_id, ci_lazy_methods_neededt lazy_methods_needed)
    {
      return convert_single_method(
        function_id, symbol_table, std::move(lazy_methods_needed));
    };

  ci_lazy_methodst method_gather(
    symbol_table,
    main_class,
    main_jar_classes,
    lazy_methods_extra_entry_points,
    java_class_loader,
    java_load_classes,
    get_pointer_type_selector(),
    get_message_handler());

  return method_gather(symbol_table, method_bytecode, method_converter);
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
void java_bytecode_languaget::methods_provided(id_sett &methods) const
{
  // Add all string solver methods to map
  string_preprocess.get_all_function_names(methods);
  // Add all concrete methods to map
  for(const auto &kv : method_bytecode)
    methods.insert(kv.first);
}

/// \brief Promote a lazy-converted method (one whose type is known but whose
/// body hasn't been converted) into a fully-elaborated one.
/// \remarks Amends the symbol table entry for function `function_id`, which
/// should be a method provided by this instance of `java_bytecode_languaget`
/// to have a value representing the method body identical to that produced
/// using eager method conversion.
/// \param function_id: method ID to convert
/// \param symtab: global symbol table
void java_bytecode_languaget::convert_lazy_method(
  const irep_idt &function_id,
  symbol_table_baset &symtab)
{
  const symbolt &symbol = symtab.lookup_ref(function_id);
  if(symbol.value.is_not_nil())
    return;

  journalling_symbol_tablet symbol_table=
    journalling_symbol_tablet::wrap(symtab);

  convert_single_method(function_id, symbol_table);

  // Instrument runtime exceptions (unless symbol is a stub)
  if(symbol.value.is_not_nil())
  {
    java_bytecode_instrument_symbol(
      symbol_table,
      symbol_table.get_writeable_ref(function_id),
      throw_runtime_exceptions,
      get_message_handler());
  }

  // now typecheck this function
  java_bytecode_typecheck_updated_symbols(
    symbol_table, get_message_handler(), string_refinement_enabled);
}

/// \brief Convert a method (one whose type is known but whose body hasn't
///   been converted) but don't run typecheck, etc
/// \remarks Amends the symbol table entry for function `function_id`, which
///   should be a method provided by this instance of `java_bytecode_languaget`
///   to have a value representing the method body.
/// \param function_id: method ID to convert
/// \param symbol_table: global symbol table
/// \param needed_lazy_methods: optionally a collection of needed methods to
///   update with any methods touched during the conversion
bool java_bytecode_languaget::convert_single_method(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods)
{
  const symbolt &symbol = symbol_table.lookup_ref(function_id);

  // Nothing to do if body is already loaded
  if(symbol.value.is_not_nil())
    return false;

  // Get bytecode for specified function if we have it
  method_bytecodet::opt_reft cmb = method_bytecode.get(function_id);

  // Check if have a string solver implementation
  if(string_preprocess.implements_function(function_id))
  {
    symbolt &symbol = symbol_table.get_writeable_ref(function_id);
    // Load parameter names from any extant bytecode before filling in body
    if(cmb)
    {
      java_bytecode_initialize_parameter_names(
        symbol, cmb->get().method.local_variable_table, symbol_table);
    }
    // Populate body of the function with code generated by string preprocess
    exprt generated_code =
      string_preprocess.code_for_function(symbol, symbol_table);
    INVARIANT(
      generated_code.is_not_nil(), "Couldn't retrieve code for string method");
    // String solver can make calls to functions that haven't yet been seen.
    // Add these to the needed_lazy_methods collection
    if(needed_lazy_methods)
    {
      for(const_depth_iteratort it = generated_code.depth_cbegin();
          it != generated_code.depth_cend();
          ++it)
      {
        if(it->id() == ID_code)
        {
          const auto fn_call = expr_try_dynamic_cast<code_function_callt>(*it);
          if(!fn_call)
            continue;
          // Only support non-virtual function calls for now, if string solver
          // starts to introduce virtual function calls then we will need to
          // duplicate the behavior of java_bytecode_convert_method where it
          // handles the invokevirtual instruction
          const symbol_exprt &fn_sym =
            expr_dynamic_cast<symbol_exprt>(fn_call->function());
          needed_lazy_methods->add_needed_method(fn_sym.get_identifier());
        }
      }
    }
    symbol.value = generated_code;
    return false;
  }

  // No string solver implementation, check if have bytecode for it
  if(cmb)
  {
    java_bytecode_convert_method(
      symbol_table.lookup_ref(cmb->get().class_id),
      cmb->get().method,
      symbol_table,
      get_message_handler(),
      max_user_array_length,
      std::move(needed_lazy_methods),
      string_preprocess);
    return false;
  }

  return true;
}

bool java_bytecode_languaget::final(symbol_table_baset &symbol_table)
{
  PRECONDITION(language_options_initialized);

  return recreate_initialize(
    symbol_table,
    main_class,
    get_message_handler(),
    assume_inputs_non_null,
    object_factory_parameters,
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
