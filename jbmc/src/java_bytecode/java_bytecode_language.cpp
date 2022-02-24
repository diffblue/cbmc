/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_language.h"

#include <fstream>
#include <string>

#include <linking/static_lifetime_init.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/expr_iterator.h>
#include <util/invariant.h>
#include <util/journalling_symbol_table.h>
#include <util/options.h>
#include <util/prefix.h>
#include <util/suffix.h>
#include <util/symbol_table.h>
#include <util/symbol_table_builder.h>

#include <json/json_parser.h>

#include <goto-programs/class_hierarchy.h>

#include "ci_lazy_methods.h"
#include "create_array_with_type_intrinsic.h"
#include "java_bytecode_concurrency_instrumentation.h"
#include "java_bytecode_convert_class.h"
#include "java_bytecode_convert_method.h"
#include "java_bytecode_instrument.h"
#include "java_bytecode_internal_additions.h"
#include "java_bytecode_typecheck.h"
#include "java_class_loader.h"
#include "java_class_loader_limit.h"
#include "java_entry_point.h"
#include "java_static_initializers.h"
#include "java_string_literal_expr.h"
#include "java_string_literals.h"
#include "java_utils.h"
#include "lambda_synthesis.h"
#include "lift_clinit_calls.h"

#include "expr2java.h"
#include "load_method_by_regex.h"

/// Parse options that are java bytecode specific.
/// \param cmd: Command line
/// \param [out] options: The options object that will be updated.
void parse_java_language_options(const cmdlinet &cmd, optionst &options)
{
  options.set_option(
    "java-assume-inputs-non-null", cmd.isset("java-assume-inputs-non-null"));
  options.set_option(
    "throw-runtime-exceptions", cmd.isset("throw-runtime-exceptions"));
  options.set_option(
    "uncaught-exception-check", !cmd.isset("disable-uncaught-exception-check"));
  options.set_option(
    "throw-assertion-error", cmd.isset("throw-assertion-error"));
  options.set_option(
    "assert-no-exceptions-thrown", cmd.isset("assert-no-exceptions-thrown"));
  options.set_option("java-threading", cmd.isset("java-threading"));

  if(cmd.isset("java-max-vla-length"))
  {
    options.set_option(
      "java-max-vla-length", cmd.get_value("java-max-vla-length"));
  }

  options.set_option(
    "symex-driven-lazy-loading", cmd.isset("symex-driven-lazy-loading"));

  options.set_option(
    "ignore-manifest-main-class", cmd.isset("ignore-manifest-main-class"));

  if(cmd.isset("context-include"))
    options.set_option("context-include", cmd.get_values("context-include"));

  if(cmd.isset("context-exclude"))
    options.set_option("context-exclude", cmd.get_values("context-exclude"));

  if(cmd.isset("java-load-class"))
    options.set_option("java-load-class", cmd.get_values("java-load-class"));

  if(cmd.isset("java-no-load-class"))
  {
    options.set_option(
      "java-no-load-class", cmd.get_values("java-no-load-class"));
  }
  if(cmd.isset("lazy-methods-extra-entry-point"))
  {
    options.set_option(
      "lazy-methods-extra-entry-point",
      cmd.get_values("lazy-methods-extra-entry-point"));
  }
  if(cmd.isset("java-cp-include-files"))
  {
    options.set_option(
      "java-cp-include-files", cmd.get_value("java-cp-include-files"));
  }
  if(cmd.isset("static-values"))
  {
    options.set_option("static-values", cmd.get_value("static-values"));
  }
  options.set_option(
    "java-lift-clinit-calls", cmd.isset("java-lift-clinit-calls"));
}

prefix_filtert get_context(const optionst &options)
{
  std::vector<std::string> context_include;
  std::vector<std::string> context_exclude;
  for(const auto &include : options.get_list_option("context-include"))
    context_include.push_back("java::" + include);
  for(const auto &exclude : options.get_list_option("context-exclude"))
    context_exclude.push_back("java::" + exclude);
  return prefix_filtert(std::move(context_include), std::move(context_exclude));
}

std::unordered_multimap<irep_idt, symbolt> &
lazy_class_to_declared_symbols_mapt::get(const symbol_tablet &symbol_table)
{
  if(!initialized)
  {
    map = class_to_declared_symbols(symbol_table);
    initialized = true;
  }
  return map;
}

void lazy_class_to_declared_symbols_mapt::reinitialize()
{
  initialized = false;
  map.clear();
}

java_bytecode_language_optionst::java_bytecode_language_optionst(
  const optionst &options,
  messaget &log)
{
  assume_inputs_non_null =
    options.get_bool_option("java-assume-inputs-non-null");
  string_refinement_enabled = options.get_bool_option("refine-strings");
  throw_runtime_exceptions =
    options.get_bool_option("throw-runtime-exceptions");
  assert_uncaught_exceptions =
    options.get_bool_option("uncaught-exception-check");
  throw_assertion_error = options.get_bool_option("throw-assertion-error");
  assert_no_exceptions_thrown =
    options.get_bool_option("assert-no-exceptions-thrown");
  threading_support = options.get_bool_option("java-threading");
  max_user_array_length =
    options.get_unsigned_int_option("java-max-vla-length");

  if(options.get_bool_option("symex-driven-lazy-loading"))
    lazy_methods_mode=LAZY_METHODS_MODE_EXTERNAL_DRIVER;
  else if(options.get_bool_option("lazy-methods"))
    lazy_methods_mode=LAZY_METHODS_MODE_CONTEXT_INSENSITIVE;
  else
    lazy_methods_mode=LAZY_METHODS_MODE_EAGER;

  if(throw_runtime_exceptions)
  {
    java_load_classes.insert(
      java_load_classes.end(),
      exception_needed_classes.begin(),
      exception_needed_classes.end());
  }

  if(options.is_set("java-load-class"))
  {
    const auto &load_values = options.get_list_option("java-load-class");
    java_load_classes.insert(
      java_load_classes.end(), load_values.begin(), load_values.end());
  }
  if(options.is_set("java-no-load-class"))
  {
    const auto &no_load_values = options.get_list_option("java-no-load-class");
    no_load_classes = {no_load_values.begin(), no_load_values.end()};
  }
  const std::list<std::string> &extra_entry_points =
    options.get_list_option("lazy-methods-extra-entry-point");
  std::transform(
    extra_entry_points.begin(),
    extra_entry_points.end(),
    std::back_inserter(extra_methods),
    build_load_method_by_regex);

  java_cp_include_files = options.get_option("java-cp-include-files");
  if(!java_cp_include_files.empty())
  {
    // load file list from JSON file
    if(java_cp_include_files[0]=='@')
    {
      jsont json_cp_config;
      if(parse_json(
           java_cp_include_files.substr(1),
           log.get_message_handler(),
           json_cp_config))
        throw "cannot read JSON input configuration for JAR loading";

      if(!json_cp_config.is_object())
        throw "the JSON file has a wrong format";
      jsont include_files=json_cp_config["jar"];
      if(!include_files.is_array())
        throw "the JSON file has a wrong format";

      // add jars from JSON config file to classpath
      for(const jsont &file_entry : to_json_array(include_files))
      {
        DATA_INVARIANT(
          file_entry.is_string() && has_suffix(file_entry.value, ".jar"),
          "classpath entry must be jar filename, but '" + file_entry.value +
          "' found");
        config.java.classpath.push_back(file_entry.value);
      }
    }
  }
  else
    java_cp_include_files=".*";

  nondet_static = options.get_bool_option("nondet-static");
  if(options.is_set("static-values"))
  {
    const std::string filename = options.get_option("static-values");
    jsont tmp_json;
    if(parse_json(filename, log.get_message_handler(), tmp_json))
    {
      log.warning()
        << "Provided JSON file for static-values cannot be parsed; it"
        << " will be ignored." << messaget::eom;
    }
    else
    {
      if(!tmp_json.is_object())
      {
        log.warning() << "Provided JSON file for static-values is not a JSON "
                      << "object; it will be ignored." << messaget::eom;
      }
      else
        static_values_json = std::move(to_json_object(tmp_json));
    }
  }

  ignore_manifest_main_class =
    options.get_bool_option("ignore-manifest-main-class");

  if(options.is_set("context-include") || options.is_set("context-exclude"))
    method_context = get_context(options);

  should_lift_clinit_calls = options.get_bool_option("java-lift-clinit-calls");
}

/// Consume options that are java bytecode specific.
void java_bytecode_languaget::set_language_options(const optionst &options)
{
  object_factory_parameters.set(options);
  language_options = java_bytecode_language_optionst{options, *this};
  const auto &new_points = build_extra_entry_points(options);
  language_options->extra_methods.insert(
    language_options->extra_methods.end(),
    new_points.begin(),
    new_points.end());
}

std::set<std::string> java_bytecode_languaget::extensions() const
{
  return { "class", "jar" };
}

void java_bytecode_languaget::modules_provided(std::set<std::string> &)
{
  // modules.insert(translation_unit(parse_path));
}

/// ANSI-C preprocessing
bool java_bytecode_languaget::preprocess(
  std::istream &,
  const std::string &,
  std::ostream &)
{
  // there is no preprocessing!
  return true;
}

void java_bytecode_languaget::set_message_handler(
  message_handlert &message_handler)
{
  languaget::set_message_handler(message_handler);
}

void java_bytecode_languaget::initialize_class_loader()
{
  java_class_loader.clear_classpath();

  for(const auto &p : config.java.classpath)
    java_class_loader.add_classpath_entry(p, get_message_handler());

  java_class_loader.set_java_cp_include_files(
    language_options->java_cp_include_files);
  java_class_loader.add_load_classes(language_options->java_load_classes);
  if(language_options->string_refinement_enabled)
  {
    string_preprocess.initialize_known_type_table();

    auto get_string_base_classes = [this](const irep_idt &id) {
      return string_preprocess.get_string_type_base_classes(id);
    };

    java_class_loader.set_extra_class_refs_function(get_string_base_classes);
  }
}

static void throwMainClassLoadingError(const std::string &main_class)
{
  throw system_exceptiont(
    "Error: Could not find or load main class " + main_class);
}

void java_bytecode_languaget::parse_from_main_class()
{
  if(!main_class.empty())
  {
    // Try to load class
    status() << "Trying to load Java main class: " << main_class << eom;
    if(!java_class_loader.can_load_class(main_class, get_message_handler()))
    {
      // Try to extract class name and load class
      const auto maybe_class_name =
        class_name_from_method_name(id2string(main_class));
      if(!maybe_class_name)
      {
        throwMainClassLoadingError(id2string(main_class));
        return;
      }
      status() << "Trying to load Java main class: " << maybe_class_name.value()
               << eom;
      if(!java_class_loader.can_load_class(
           maybe_class_name.value(), get_message_handler()))
      {
        throwMainClassLoadingError(id2string(main_class));
        return;
      }
      // Everything went well. We have a loadable main class.
      // The entry point ('main') will be checked later.
      config.main = id2string(main_class);
      main_class = maybe_class_name.value();
    }
    status() << "Found Java main class: " << main_class << eom;
    // Now really load it.
    const auto &parse_trees =
      java_class_loader(main_class, get_message_handler());
    if(parse_trees.empty() || !parse_trees.front().loading_successful)
    {
      throwMainClassLoadingError(id2string(main_class));
    }
  }
}

/// We set the main class (i.e.\ class to start the class loading analysis,
/// see \ref java_class_loadert) when we have have been given a main class.
bool java_bytecode_languaget::parse()
{
  PRECONDITION(language_options.has_value());
  initialize_class_loader();
  main_class = config.java.main_class;
  parse_from_main_class();
  return false;
}

/// We set the main class (i.e.\ class to start the class loading analysis,
/// see \ref java_class_loadert)
/// when we have a JAR file given via the -jar option:
///    a) the argument of the --main-class command-line option,
///    b) the manifest file of the JAR
///    If no main class was found, all classes in the JAR file are loaded.
bool java_bytecode_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  PRECONDITION(language_options.has_value());
  initialize_class_loader();

  // look at extension
  if(has_suffix(path, ".jar"))
  {
    std::ifstream jar_file(path);
    if(!jar_file.good())
    {
      throw system_exceptiont("Error: Unable to access jarfile " + path);
    }

    // build an object to potentially limit which classes are loaded
    java_class_loader_limitt class_loader_limit(
      get_message_handler(), language_options->java_cp_include_files);
    if(config.java.main_class.empty())
    {
      // If we have an entry method, we can derive a main class.
      if(config.main.has_value())
      {
        const std::string &entry_method = config.main.value();
        const auto last_dot_position = entry_method.find_last_of('.');
        main_class = entry_method.substr(0, last_dot_position);
      }
      else
      {
        auto manifest = java_class_loader.jar_pool(path).get_manifest();
        std::string manifest_main_class = manifest["Main-Class"];

        // if the manifest declares a Main-Class line, we got a main class
        if(
          !manifest_main_class.empty() &&
          !language_options->ignore_manifest_main_class)
        {
          main_class = manifest_main_class;
        }
      }
    }
    else
      main_class=config.java.main_class;

    // do we have one now?
    if(main_class.empty())
    {
      status() << "JAR file without entry point: loading class files" << eom;
      const auto classes =
        java_class_loader.load_entire_jar(path, get_message_handler());
      for(const auto &c : classes)
        main_jar_classes.push_back(c);
    }
    else
      java_class_loader.add_classpath_entry(path, get_message_handler());
  }
  else
    main_class = config.java.main_class;

  parse_from_main_class();
  return false;
}

/// Infer fields that must exist on opaque types from field accesses against
/// them. Note that we don't yet try to infer inheritence between opaque types
/// here, so we may introduce the same field onto a type and its ancestor
/// without realising that is in fact the same field, inherited from that
/// ancestor. This can lead to incorrect results when opaque types are cast
/// to other opaque types and their fields do not alias as intended.
/// We set opaque fields as final to avoid assuming they can be overridden.
/// \param parse_tree: class parse tree
/// \param symbol_table: global symbol table
static void infer_opaque_type_fields(
  const java_bytecode_parse_treet &parse_tree,
  symbol_tablet &symbol_table)
{
  namespacet ns(symbol_table);
  for(const auto &method : parse_tree.parsed_class.methods)
  {
    for(const java_bytecode_parse_treet::instructiont &instruction :
          method.instructions)
    {
      const std::string statement =
        bytecode_info[instruction.bytecode].mnemonic;
      if(statement == "getfield" || statement == "putfield")
      {
        const fieldref_exprt &fieldref =
          expr_dynamic_cast<fieldref_exprt>(instruction.args[0]);
        irep_idt class_symbol_id = fieldref.class_name();
        const symbolt *class_symbol = symbol_table.lookup(class_symbol_id);
        INVARIANT(
          class_symbol != nullptr,
          "all types containing fields should have been loaded");

        const java_class_typet *class_type =
          &to_java_class_type(class_symbol->type);
        const irep_idt &component_name = fieldref.component_name();
        while(!class_type->has_component(component_name))
        {
          if(class_type->get_is_stub())
          {
            // Accessing a field of an incomplete (opaque) type.
            symbolt &writable_class_symbol =
              symbol_table.get_writeable_ref(class_symbol_id);
            auto &components =
              to_java_class_type(writable_class_symbol.type).components();
            components.emplace_back(component_name, fieldref.type());
            components.back().set_base_name(component_name);
            components.back().set_pretty_name(component_name);
            components.back().set_is_final(true);
            break;
          }
          else
          {
            // Not present here: check the superclass.
            INVARIANT(
              !class_type->bases().empty(),
              "class '" + id2string(class_symbol->name) +
                "' (which was missing a field '" + id2string(component_name) +
                "' referenced from method '" + id2string(method.name) +
                "' of class '" + id2string(parse_tree.parsed_class.name) +
                "') should have an opaque superclass");
            const auto &superclass_type = class_type->bases().front().type();
            class_symbol_id = superclass_type.get_identifier();
            class_type = &to_java_class_type(ns.follow(superclass_type));
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
  struct_tag_typet java_lang_Class("java::java.lang.Class");
  symbol_exprt symbol_expr(
    id2string(class_id) + JAVA_CLASS_MODEL_SUFFIX,
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
    new_class_symbol.type.set(ID_C_no_nondet_initialization, true);
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
  else if(
    const auto &literal =
      expr_try_dynamic_cast<java_string_literal_exprt>(ldc_arg0))
  {
    return address_of_exprt(get_or_create_string_literal_symbol(
      *literal, symbol_table, string_refinement_enabled));
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
    for(java_bytecode_parse_treet::instructiont &instruction :
          method.instructions)
    {
      // ldc* instructions are Java bytecode "load constant" ops, which can
      // retrieve a numeric constant, String literal, or Class literal.
      const std::string statement =
        bytecode_info[instruction.bytecode].mnemonic;
      // clang-format off
      if(statement == "ldc" ||
         statement == "ldc2" ||
         statement == "ldc_w" ||
         statement == "ldc2_w")
      {
        // clang-format on
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

/// Add a stub global symbol to the symbol table, initialising pointer-typed
/// symbols with null and primitive-typed ones with an arbitrary (nondet) value.
/// \param symbol_table: table to add to
/// \param symbol_id: new symbol fully-qualified identifier
/// \param symbol_basename: new symbol basename
/// \param symbol_type: new symbol type
/// \param class_id: class id that directly encloses this static field
/// \param force_nondet_init: if true, always leave the symbol's value nil so it
///   gets nondet initialized during __CPROVER_initialize. Otherwise, pointer-
///   typed globals are initialized null and we expect a synthetic clinit method
///   to be created later.
static void create_stub_global_symbol(
  symbol_table_baset &symbol_table,
  const irep_idt &symbol_id,
  const irep_idt &symbol_basename,
  const typet &symbol_type,
  const irep_idt &class_id,
  bool force_nondet_init)
{
  symbolt new_symbol;
  new_symbol.is_static_lifetime = true;
  new_symbol.is_lvalue = true;
  new_symbol.is_state_var = true;
  new_symbol.name = symbol_id;
  new_symbol.base_name = symbol_basename;
  new_symbol.type = symbol_type;
  set_declaring_class(new_symbol, class_id);
  // Public access is a guess; it encourages merging like-typed static fields,
  // whereas a more restricted visbility would encourage separating them.
  // Neither is correct, as without the class file we can't know the truth.
  new_symbol.type.set(ID_C_access, ID_public);
  // We set the field as final to avoid assuming they can be overridden.
  new_symbol.type.set(ID_C_constant, true);
  new_symbol.pretty_name = new_symbol.name;
  new_symbol.mode = ID_java;
  new_symbol.is_type = false;
  // If pointer-typed, initialise to null and a static initialiser will be
  // created to initialise on first reference. If primitive-typed, specify
  // nondeterministic initialisation by setting a nil value.
  if(symbol_type.id() == ID_pointer && !force_nondet_init)
    new_symbol.value = null_pointer_exprt(to_pointer_type(symbol_type));
  else
    new_symbol.value.make_nil();
  bool add_failed = symbol_table.add(new_symbol);
  INVARIANT(
    !add_failed, "caller should have checked symbol not already in table");
}

/// Find any incomplete ancestor of a given class that can have a stub static
/// field attached to it. This specifically excludes java.lang.Object, which we
/// know cannot have static fields.
/// \param start_class_id: class to start searching from
/// \param symbol_table: global symbol table
/// \param class_hierarchy: global class hierarchy
/// \return first incomplete ancestor encountered,
///   including start_class_id itself.
static irep_idt get_any_incomplete_ancestor_for_stub_static_field(
  const irep_idt &start_class_id,
  const symbol_tablet &symbol_table,
  const class_hierarchyt &class_hierarchy)
{
  // Depth-first search: return the first stub ancestor, or irep_idt() if none
  // found.
  std::vector<irep_idt> classes_to_check;
  classes_to_check.push_back(start_class_id);

  while(!classes_to_check.empty())
  {
    irep_idt to_check = classes_to_check.back();
    classes_to_check.pop_back();

    // Exclude java.lang.Object because it can
    if(
      to_java_class_type(symbol_table.lookup_ref(to_check).type)
        .get_is_stub() &&
      to_check != "java::java.lang.Object")
    {
      return to_check;
    }

    const class_hierarchyt::idst &parents =
      class_hierarchy.class_map.at(to_check).parents;
    classes_to_check.insert(
      classes_to_check.end(), parents.begin(), parents.end());
  }

  return irep_idt();
}

/// Search for getstatic and putstatic instructions in a class' bytecode and
/// create stub symbols for any static fields that aren't already in the symbol
/// table. The new symbols are null-initialized for reference-typed globals /
/// static fields, and nondet-initialized for primitives.
/// \param parse_tree: class bytecode
/// \param symbol_table: symbol table; may gain new symbols
/// \param class_hierarchy: global class hierarchy
/// \param log: message handler used to log warnings when stub static fields are
///   found belonging to non-stub classes.
static void create_stub_global_symbols(
  const java_bytecode_parse_treet &parse_tree,
  symbol_table_baset &symbol_table,
  const class_hierarchyt &class_hierarchy,
  messaget &log)
{
  namespacet ns(symbol_table);
  for(const auto &method : parse_tree.parsed_class.methods)
  {
    for(const java_bytecode_parse_treet::instructiont &instruction :
          method.instructions)
    {
      const std::string statement =
        bytecode_info[instruction.bytecode].mnemonic;
      if(statement == "getstatic" || statement == "putstatic")
      {
        INVARIANT(
          instruction.args.size() > 0,
          "get/putstatic should have at least one argument");
        const fieldref_exprt &field_ref =
          expr_dynamic_cast<fieldref_exprt>(instruction.args[0]);
        irep_idt component = field_ref.component_name();
        irep_idt class_id = field_ref.class_name();

        // The final 'true' parameter here includes interfaces, as they can
        // define static fields.
        const auto referred_component =
          get_inherited_component(class_id, component, symbol_table, true);
        if(!referred_component)
        {
          // Create a new stub global on an arbitrary incomplete ancestor of the
          // class that was referred to. This is just a guess, but we have no
          // better information to go on.
          irep_idt add_to_class_id =
            get_any_incomplete_ancestor_for_stub_static_field(
              class_id, symbol_table, class_hierarchy);

          // If there are no incomplete ancestors to ascribe the missing field
          // to, we must have an incomplete model of a class or simply a
          // version mismatch of some kind. Normally this would be an error, but
          // our models library currently triggers this error in some cases
          // (notably java.lang.System, which is missing System.in/out/err).
          // Therefore for this case we ascribe the missing field to the class
          // it was directly referenced from, and fall back to initialising the
          // field in __CPROVER_initialize, rather than try to create or augment
          // a clinit method for a non-stub class.

          bool no_incomplete_ancestors = add_to_class_id.empty();
          if(no_incomplete_ancestors)
          {
            add_to_class_id = class_id;

            // TODO forbid this again once the models library has been checked
            // for missing static fields.
            log.warning() << "Stub static field " << component << " found for "
                          << "non-stub type " << class_id << ". In future this "
                          << "will be a fatal error." << messaget::eom;
          }

          irep_idt identifier =
            id2string(add_to_class_id) + "." + id2string(component);

          create_stub_global_symbol(
            symbol_table,
            identifier,
            component,
            instruction.args[0].type(),
            add_to_class_id,
            no_incomplete_ancestors);
        }
      }
    }
  }
}

bool java_bytecode_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &)
{
  PRECONDITION(language_options.has_value());
  // There are various cases in the Java front-end where pre-existing symbols
  // from a previous load are not handled. We just rule this case out for now;
  // a user wishing to ensure a particular class is loaded should use
  // --java-load-class (to force class-loading) or
  // --lazy-methods-extra-entry-point (to ensure a method body is loaded)
  // instead of creating two instances of the front-end.
  INVARIANT(
    symbol_table.begin() == symbol_table.end(),
    "the Java front-end should only be used with an empty symbol table");

  java_internal_additions(symbol_table);
  create_java_initialize(symbol_table);

  if(language_options->string_refinement_enabled)
    string_preprocess.initialize_conversion_table();

  // Must load java.lang.Object first to avoid stubbing
  // This ordering could alternatively be enforced by
  // moving the code below to the class loader.
  java_class_loadert::parse_tree_with_overridest_mapt::const_iterator it =
    java_class_loader.get_class_with_overlays_map().find("java.lang.Object");
  if(it != java_class_loader.get_class_with_overlays_map().end())
  {
    if(java_bytecode_convert_class(
         it->second,
         symbol_table,
         get_message_handler(),
         language_options->max_user_array_length,
         method_bytecode,
         string_preprocess,
         language_options->no_load_classes))
    {
      return true;
    }
  }

  // first generate a new struct symbol for each class and a new function symbol
  // for every method
  for(const auto &class_trees : java_class_loader.get_class_with_overlays_map())
  {
    if(class_trees.second.front().parsed_class.name.empty())
      continue;

    if(java_bytecode_convert_class(
         class_trees.second,
         symbol_table,
         get_message_handler(),
         language_options->max_user_array_length,
         method_bytecode,
         string_preprocess,
         language_options->no_load_classes))
    {
      return true;
    }
  }

  // Register synthetic method that replaces a real definition if one is
  // available:
  if(symbol_table.has_symbol(get_create_array_with_type_name()))
  {
    synthetic_methods[get_create_array_with_type_name()] =
      synthetic_method_typet::CREATE_ARRAY_WITH_TYPE;
  }

  // Now add synthetic classes for every invokedynamic instruction found (it
  // makes this easier that all interface types and their methods have been
  // created above):
  {
    std::vector<irep_idt> methods_to_check;

    // Careful not to add to the symtab while iterating over it:
    for(const auto &id_and_symbol : symbol_table)
    {
      const auto &symbol = id_and_symbol.second;
      const auto &id = symbol.name;
      if(can_cast_type<code_typet>(symbol.type) && method_bytecode.get(id))
      {
        methods_to_check.push_back(id);
      }
    }

    for(const auto &id : methods_to_check)
    {
      create_invokedynamic_synthetic_classes(
        id,
        method_bytecode.get(id)->get().method.instructions,
        symbol_table,
        synthetic_methods,
        get_message_handler());
    }
  }

  // Now that all classes have been created in the symbol table we can populate
  // the class hierarchy:
  class_hierarchy(symbol_table);

  // find and mark all implicitly generic class types
  // this can only be done once all the class symbols have been created
  for(const auto &c : java_class_loader.get_class_with_overlays_map())
  {
    if(c.second.front().parsed_class.name.empty())
      continue;
    try
    {
      mark_java_implicitly_generic_class_type(
        c.second.front().parsed_class.name, symbol_table);
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
  for(auto &class_to_trees : java_class_loader.get_class_with_overlays_map())
  {
    for(const java_bytecode_parse_treet &parse_tree : class_to_trees.second)
      infer_opaque_type_fields(parse_tree, symbol_table);
  }

  // Create global variables for constants (String and Class literals) up front.
  // This means that when running with lazy loading, we will be aware of these
  // literal globals' existence when __CPROVER_initialize is generated in
  // `generate_support_functions`.
  const std::size_t before_constant_globals_size = symbol_table.symbols.size();
  for(auto &class_to_trees : java_class_loader.get_class_with_overlays_map())
  {
    for(java_bytecode_parse_treet &parse_tree : class_to_trees.second)
    {
      generate_constant_global_variables(
        parse_tree, symbol_table, language_options->string_refinement_enabled);
    }
  }
  status() << "Java: added "
           << (symbol_table.symbols.size() - before_constant_globals_size)
           << " String or Class constant symbols"
           << messaget::eom;

  // For each reference to a stub global (that is, a global variable declared on
  // a class we don't have bytecode for, and therefore don't know the static
  // initialiser for), create a synthetic static initialiser (clinit method)
  // to nondet initialise it.
  // Note this must be done before making static initialiser wrappers below, as
  // this makes a Classname.clinit method, then the next pass makes a wrapper
  // that ensures it is only run once, and that static initialisation happens
  // in class-graph topological order.

  {
    journalling_symbol_tablet symbol_table_journal =
      journalling_symbol_tablet::wrap(symbol_table);
    for(auto &class_to_trees : java_class_loader.get_class_with_overlays_map())
    {
      for(const java_bytecode_parse_treet &parse_tree : class_to_trees.second)
      {
        create_stub_global_symbols(
          parse_tree, symbol_table_journal, class_hierarchy, *this);
      }
    }

    stub_global_initializer_factory.create_stub_global_initializer_symbols(
      symbol_table, symbol_table_journal.get_inserted(), synthetic_methods);
  }

  create_static_initializer_symbols(
    symbol_table,
    synthetic_methods,
    language_options->threading_support,
    language_options->static_values_json.has_value());

  lazy_class_to_declared_symbols_mapt class_to_declared_symbols;

  // Now incrementally elaborate methods
  // that are reachable from this entry point.
  switch(language_options->lazy_methods_mode)
  {
  case LAZY_METHODS_MODE_CONTEXT_INSENSITIVE:
    // ci = context-insensitive
    if(do_ci_lazy_method_conversion(symbol_table))
      return true;
    break;
  case LAZY_METHODS_MODE_EAGER:
  {
    symbol_table_buildert symbol_table_builder =
      symbol_table_buildert::wrap(symbol_table);

    journalling_symbol_tablet journalling_symbol_table =
      journalling_symbol_tablet::wrap(symbol_table_builder);

    // Convert all synthetic methods:
    for(const auto &function_id_and_type : synthetic_methods)
    {
      convert_single_method(
        function_id_and_type.first,
        journalling_symbol_table,
        class_to_declared_symbols);
    }
    // Convert all methods for which we have bytecode now
    for(const auto &method_sig : method_bytecode)
    {
      convert_single_method(
        method_sig.first, journalling_symbol_table, class_to_declared_symbols);
    }
    convert_single_method(
      INITIALIZE_FUNCTION, journalling_symbol_table, class_to_declared_symbols);
    // Now convert all newly added string methods
    for(const auto &fn_name : journalling_symbol_table.get_inserted())
    {
      if(string_preprocess.implements_function(fn_name))
        convert_single_method(fn_name, symbol_table, class_to_declared_symbols);
    }
  }
  break;
  case LAZY_METHODS_MODE_EXTERNAL_DRIVER:
    // Our caller is in charge of elaborating methods on demand.
    break;
  }

  // now instrument runtime exceptions
  java_bytecode_instrument(
    symbol_table,
    language_options->throw_runtime_exceptions,
    get_message_handler());

  // now typecheck all
  bool res = java_bytecode_typecheck(
    symbol_table,
    get_message_handler(),
    language_options->string_refinement_enabled);

  // now instrument thread-blocks and synchronized methods.
  if(language_options->threading_support)
  {
    convert_threadblock(symbol_table);
    convert_synchronized_methods(symbol_table, get_message_handler());
  }

  return res;
}

bool java_bytecode_languaget::generate_support_functions(
  symbol_tablet &symbol_table)
{
  PRECONDITION(language_options.has_value());

  symbol_table_buildert symbol_table_builder =
    symbol_table_buildert::wrap(symbol_table);

  main_function_resultt res=
    get_main_symbol(symbol_table, main_class, get_message_handler());
  if(!res.is_success())
    return res.is_error();

  // Load the main function into the symbol table to get access to its
  // parameter names
  convert_lazy_method(res.main_function.name, symbol_table_builder);

  const symbolt &symbol =
    symbol_table_builder.lookup_ref(res.main_function.name);
  if(symbol.value.is_nil())
  {
    throw invalid_command_line_argument_exceptiont(
      "the program has no entry point",
      "function",
      "Check that the specified entry point is included by your "
      "--context-include or --context-exclude options");
  }

  // generate the test harness in __CPROVER__start and a call the entry point
  return java_entry_point(
    symbol_table_builder,
    main_class,
    get_message_handler(),
    language_options->assume_inputs_non_null,
    language_options->assert_uncaught_exceptions,
    object_factory_parameters,
    get_pointer_type_selector(),
    language_options->string_refinement_enabled,
    [&](const symbolt &function, symbol_table_baset &symbol_table) {
      return java_build_arguments(
        function,
        symbol_table,
        language_options->assume_inputs_non_null,
        object_factory_parameters,
        get_pointer_type_selector(),
        get_message_handler());
    });
}

/// Uses a simple context-insensitive ('ci') analysis to determine which methods
/// may be reachable from the main entry point. In brief, static methods are
/// reachable if we find a callsite in another reachable site, while virtual
/// methods are reachable if we find a virtual callsite targeting a compatible
/// type *and* a constructor callsite indicating an object of that type may be
/// instantiated (or evidence that an object of that type exists before the main
/// function is entered, such as being passed as a parameter).
/// \param symbol_table: global symbol table
/// \return Elaborates lazily-converted methods that may be reachable starting
///   from the main entry point (usually provided with the --function command-
///   line option) (side-effect on the symbol_table). Returns false on success.
bool java_bytecode_languaget::do_ci_lazy_method_conversion(
  symbol_tablet &symbol_table)
{
  symbol_table_buildert symbol_table_builder =
    symbol_table_buildert::wrap(symbol_table);

  lazy_class_to_declared_symbols_mapt class_to_declared_symbols;

  const method_convertert method_converter =
    [this, &symbol_table_builder, &class_to_declared_symbols](
      const irep_idt &function_id,
      ci_lazy_methods_neededt lazy_methods_needed) {
      return convert_single_method(
        function_id,
        symbol_table_builder,
        std::move(lazy_methods_needed),
        class_to_declared_symbols);
    };

  ci_lazy_methodst method_gather(
    symbol_table,
    main_class,
    main_jar_classes,
    language_options->extra_methods,
    java_class_loader,
    language_options->java_load_classes,
    get_pointer_type_selector(),
    synthetic_methods);

  return method_gather(
    symbol_table, method_bytecode, method_converter, get_message_handler());
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
void java_bytecode_languaget::methods_provided(
  std::unordered_set<irep_idt> &methods) const
{
  const std::string cprover_class_prefix = "java::org.cprover.CProver.";

  // Add all string solver methods to map
  string_preprocess.get_all_function_names(methods);
  // Add all concrete methods to map
  for(const auto &kv : method_bytecode)
    methods.insert(kv.first);
  // Add all synthetic methods to map
  for(const auto &kv : synthetic_methods)
    methods.insert(kv.first);
  methods.insert(INITIALIZE_FUNCTION);
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

  lazy_class_to_declared_symbols_mapt class_to_declared_symbols;
  convert_single_method(function_id, symbol_table, class_to_declared_symbols);

  // Instrument runtime exceptions (unless symbol is a stub or is the
  // INITIALISE_FUNCTION).
  if(symbol.value.is_not_nil() && function_id != INITIALIZE_FUNCTION)
  {
    java_bytecode_instrument_symbol(
      symbol_table,
      symbol_table.get_writeable_ref(function_id),
      language_options->throw_runtime_exceptions,
      get_message_handler());
  }

  // now typecheck this function
  java_bytecode_typecheck_updated_symbols(
    symbol_table,
    get_message_handler(),
    language_options->string_refinement_enabled);
}

/// Notify ci_lazy_methods, if present, of any static function calls made by
/// the given function body.
/// Note only static function calls need to be reported -- virtual function
/// calls are routinely found by searching the function body after conversion
/// because we can only approximate the possible callees once all function
/// bodies currently believed to be needed have been loaded.
/// \param function_body: function body code
/// \param needed_lazy_methods: optional ci_lazy_method_neededt interface. If
///   not set, this is a no-op; otherwise, its add_needed_method function will
///   be called for each function call in `function_body`.
static void notify_static_method_calls(
  const codet &function_body,
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods)
{
  if(needed_lazy_methods)
  {
    for(const_depth_iteratort it = function_body.depth_cbegin();
        it != function_body.depth_cend();
        ++it)
    {
      if(it->id() == ID_code)
      {
        const auto fn_call = expr_try_dynamic_cast<code_function_callt>(*it);
        if(!fn_call)
          continue;
        const symbol_exprt *fn_sym =
          expr_try_dynamic_cast<symbol_exprt>(fn_call->function());
        if(fn_sym)
          needed_lazy_methods->add_needed_method(fn_sym->get_identifier());
      }
      else if(
        it->id() == ID_side_effect &&
        to_side_effect_expr(*it).get_statement() == ID_function_call)
      {
        const auto &call_expr = to_side_effect_expr_function_call(*it);
        const symbol_exprt *fn_sym =
          expr_try_dynamic_cast<symbol_exprt>(call_expr.function());
        if(fn_sym)
        {
          INVARIANT(
            false,
            "Java synthetic methods are not "
            "expected to produce side_effect_expr_function_callt. If "
            "that has changed, remove this invariant. Also note that "
            "as of the time of writing remove_virtual_functions did "
            "not support this form of function call.");
          // needed_lazy_methods->add_needed_method(fn_sym->get_identifier());
        }
      }
    }
  }
}

/// \brief Convert a method (one whose type is known but whose body hasn't
///   been converted) if it doesn't already have a body, and lift clinit calls
///   if requested by the user.
/// \remarks Amends the symbol table entry for function `function_id`, which
///   should be a method provided by this instance of `java_bytecode_languaget`
///   to have a value representing the method body.
/// \param function_id: method ID to convert
/// \param symbol_table: global symbol table
/// \param needed_lazy_methods: optionally a collection of needed methods to
///   update with any methods touched during the conversion
/// \param class_to_declared_symbols: maps classes to the symbols that
///   they declare.
bool java_bytecode_languaget::convert_single_method(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
  lazy_class_to_declared_symbols_mapt &class_to_declared_symbols)
{
  const symbolt &symbol = symbol_table.lookup_ref(function_id);

  // Nothing to do if body is already loaded
  if(symbol.value.is_not_nil())
    return false;

  if(function_id == INITIALIZE_FUNCTION)
  {
    java_static_lifetime_init(
      symbol_table,
      symbol.location,
      language_options->assume_inputs_non_null,
      object_factory_parameters,
      *pointer_type_selector,
      language_options->string_refinement_enabled,
      get_message_handler());
    return false;
  }

  INVARIANT(declaring_class(symbol), "Method must have a declaring class.");

  bool ret = convert_single_method_code(
    function_id, symbol_table, needed_lazy_methods, class_to_declared_symbols);

  if(symbol.value.is_not_nil() && language_options->should_lift_clinit_calls)
  {
    auto &writable_symbol = symbol_table.get_writeable_ref(function_id);
    writable_symbol.value =
      lift_clinit_calls(std::move(to_code(writable_symbol.value)));
  }

  INVARIANT(declaring_class(symbol), "Method must have a declaring class.");

  return ret;
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
/// \param class_to_declared_symbols: maps classes to the symbols that
///   they declare.
bool java_bytecode_languaget::convert_single_method_code(
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
  lazy_class_to_declared_symbols_mapt &class_to_declared_symbols)
{
  const auto &symbol = symbol_table.lookup_ref(function_id);
  PRECONDITION(symbol.value.is_nil());

  // Get bytecode for specified function if we have it
  method_bytecodet::opt_reft cmb = method_bytecode.get(function_id);

  synthetic_methods_mapt::iterator synthetic_method_it;

  // Check if have a string solver implementation
  if(string_preprocess.implements_function(function_id))
  {
    symbolt &writable_symbol = symbol_table.get_writeable_ref(function_id);
    // Load parameter names from any extant bytecode before filling in body
    if(cmb)
    {
      java_bytecode_initialize_parameter_names(
        writable_symbol, cmb->get().method.local_variable_table, symbol_table);
    }
    // Populate body of the function with code generated by string preprocess
    codet generated_code = string_preprocess.code_for_function(
      writable_symbol, symbol_table, get_message_handler());
    // String solver can make calls to functions that haven't yet been seen.
    // Add these to the needed_lazy_methods collection
    notify_static_method_calls(generated_code, needed_lazy_methods);
    writable_symbol.value = std::move(generated_code);
    return false;
  }
  else if(
    (synthetic_method_it = synthetic_methods.find(function_id)) !=
    synthetic_methods.end())
  {
    // Synthetic method (i.e. one generated by the Java frontend and which
    // doesn't occur in the source bytecode):
    symbolt &writable_symbol = symbol_table.get_writeable_ref(function_id);
    switch(synthetic_method_it->second)
    {
    case synthetic_method_typet::STATIC_INITIALIZER_WRAPPER:
      if(language_options->threading_support)
        writable_symbol.value = get_thread_safe_clinit_wrapper_body(
          function_id,
          symbol_table,
          language_options->nondet_static,
          language_options->static_values_json.has_value(),
          object_factory_parameters,
          get_pointer_type_selector(),
          get_message_handler());
      else
        writable_symbol.value = get_clinit_wrapper_body(
          function_id,
          symbol_table,
          language_options->nondet_static,
          language_options->static_values_json.has_value(),
          object_factory_parameters,
          get_pointer_type_selector(),
          get_message_handler());
      break;
    case synthetic_method_typet::USER_SPECIFIED_STATIC_INITIALIZER:
    {
      const auto class_name =
        declaring_class(symbol_table.lookup_ref(function_id));
      INVARIANT(
        class_name, "user_specified_clinit must be declared by a class.");
      INVARIANT(
        language_options->static_values_json.has_value(),
        "static-values JSON must be available");
      writable_symbol.value = get_user_specified_clinit_body(
        *class_name,
        *language_options->static_values_json,
        symbol_table,
        needed_lazy_methods,
        language_options->max_user_array_length,
        references,
        class_to_declared_symbols.get(symbol_table));
      break;
    }
    case synthetic_method_typet::STUB_CLASS_STATIC_INITIALIZER:
      writable_symbol.value =
        stub_global_initializer_factory.get_stub_initializer_body(
          function_id,
          symbol_table,
          object_factory_parameters,
          get_pointer_type_selector(),
          get_message_handler());
      break;
    case synthetic_method_typet::INVOKEDYNAMIC_CAPTURE_CONSTRUCTOR:
      writable_symbol.value = invokedynamic_synthetic_constructor(
        function_id, symbol_table, get_message_handler());
      break;
    case synthetic_method_typet::INVOKEDYNAMIC_METHOD:
      writable_symbol.value = invokedynamic_synthetic_method(
        function_id, symbol_table, get_message_handler());
      break;
    case synthetic_method_typet::CREATE_ARRAY_WITH_TYPE:
    {
      INVARIANT(
        cmb,
        "CProver.createArrayWithType should only be registered if "
        "we have a real implementation available");
      java_bytecode_initialize_parameter_names(
        writable_symbol, cmb->get().method.local_variable_table, symbol_table);
      writable_symbol.value = create_array_with_type_body(
        function_id, symbol_table, get_message_handler());
      break;
    }
    }
    // Notify lazy methods of static calls made from the newly generated
    // function:
    notify_static_method_calls(
      to_code(writable_symbol.value), needed_lazy_methods);
    return false;
  }

  // No string solver or static init wrapper implementation;
  // check if have bytecode for it
  if(cmb)
  {
    java_bytecode_convert_method(
      symbol_table.lookup_ref(cmb->get().class_id),
      cmb->get().method,
      symbol_table,
      get_message_handler(),
      language_options->max_user_array_length,
      language_options->throw_assertion_error,
      std::move(needed_lazy_methods),
      string_preprocess,
      class_hierarchy,
      language_options->threading_support,
      language_options->method_context,
      language_options->assert_no_exceptions_thrown);
    return false;
  }

  if(needed_lazy_methods)
  {
    // The return of an opaque function is a source of an otherwise invisible
    // instantiation, so here we ensure we've loaded the appropriate classes.
    const java_method_typet function_type = to_java_method_type(symbol.type);
    if(
      const pointer_typet *pointer_return_type =
        type_try_dynamic_cast<pointer_typet>(function_type.return_type()))
    {
      // If the return type is abstract, we won't forcibly instantiate it here
      // otherwise this can cause abstract methods to be explictly called
      // TODO(tkiley): Arguably no abstract class should ever be added to
      // TODO(tkiley): ci_lazy_methods_neededt, but this needs further
      // TODO(tkiley): investigation
      namespacet ns{symbol_table};
      const java_class_typet &underlying_type =
        to_java_class_type(ns.follow(pointer_return_type->base_type()));

      if(!underlying_type.is_abstract())
        needed_lazy_methods->add_all_needed_classes(*pointer_return_type);
    }
  }

  return true;
}

bool java_bytecode_languaget::final(symbol_table_baset &)
{
  PRECONDITION(language_options.has_value());
  return false;
}

void java_bytecode_languaget::show_parse(std::ostream &out)
{
  java_class_loadert::parse_tree_with_overlayst &parse_trees =
    java_class_loader(main_class, get_message_handler());
  parse_trees.front().output(out);
  if(parse_trees.size() > 1)
  {
    out << "\n\nClass has the following overlays:\n\n";
    for(auto parse_tree_it = std::next(parse_trees.begin());
      parse_tree_it != parse_trees.end();
      ++parse_tree_it)
    {
      parse_tree_it->output(out);
    }
    out << "End of class overlays.\n";
  }
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
#else
  // unused parameters
  (void)code;
  (void)module;
  (void)expr;
  (void)ns;
#endif

  return true; // fail for now
}

java_bytecode_languaget::~java_bytecode_languaget()
{
}

/// This method should be overloaded to provide alternative approaches for
/// specifying extra entry points. To provide a regex entry point, the command
/// line option `--lazy-methods-extra-entry-point` can be used directly.
std::vector<load_extra_methodst>
java_bytecode_languaget::build_extra_entry_points(const optionst &options) const
{
  (void)options; // unused parameter
  return {};
}
