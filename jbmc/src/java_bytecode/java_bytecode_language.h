/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H

#include <util/json.h>
#include <util/make_unique.h>
#include <util/prefix_filter.h>
#include <util/symbol.h> // IWYU pragma: keep

#include <langapi/language.h>

#include "ci_lazy_methods.h"
#include "ci_lazy_methods_needed.h"
#include "code_with_references.h" // IWYU pragma: keep
#include "java_class_loader.h"
#include "java_object_factory_parameters.h"
#include "java_static_initializers.h"
#include "java_string_library_preprocess.h"
#include "select_pointer_type.h"
#include "synthetic_methods_map.h"

#include <memory>

// clang-format off
#define JAVA_BYTECODE_LANGUAGE_OPTIONS /*NOLINT*/ \
  "(disable-uncaught-exception-check)" \
  "(throw-assertion-error)" \
  "(assert-no-exceptions-thrown)" \
  "(java-assume-inputs-non-null)" \
  "(java-assume-inputs-interval):" \
  "(java-assume-inputs-integral)" \
  "(throw-runtime-exceptions)" \
  "(max-nondet-array-length):" \
  "(max-nondet-tree-depth):" \
  "(java-max-vla-length):" \
  "(java-cp-include-files):" \
  "(ignore-manifest-main-class)" \
  "(context-include):" \
  "(context-exclude):" \
  "(no-lazy-methods)" \
  "(lazy-methods-extra-entry-point):" \
  "(java-load-class):" \
  "(java-no-load-class):" \
  "(static-values):" \
  "(java-lift-clinit-calls)"

#define JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP /*NOLINT*/ \
  help_entry( \
    "--disable-uncaught-exception-check", \
    "ignore uncaught exceptions and errors") \
  << help_entry( \
    "--throw-assertion-error", \
    "throw java.lang.AssertionError on violated assert statements instead of " \
    "failing at the location of the assert statement") \
  << help_entry( \
    "--throw-runtime-exceptions", \
    "make implicit runtime exceptions explicit") \
  << help_entry( \
    "--assert-no-exceptions-thrown", \
    "transform `throw` instructions into `assert FALSE` followed by `assume " \
    "FALSE`.") \
  << help_entry( \
    "--max-nondet-array-length N", \
    "limit nondet (e.g. input) array size to <= N") \
  << help_entry( \
    "--max-nondet-tree-depth N", \
    "limit size of nondet (e.g. input) object tree; at level N references " \
    "are set to null") \
  << help_entry( \
    "--java-assume-inputs-non-null", \
    "never initialize reference-typed parameter to the entry point with null") \
  << help_entry( \
    "--java-assume-inputs-interval [L:U] or [L:] or [:U]", \
    "force numerical primitive-typed inputs (byte, short, int, long, float, " \
    "double) to be initialized within the given range; lower bound L and " \
    "upper bound U must be integers; does not work for arrays;") \
  << help_entry( \
    "--java-assume-inputs-integral", \
    "force float and double inputs to have integer values; does not work for " \
    "arrays;") \
  << help_entry( \
    "--java-max-vla-length N", \
    "limit the length of user-code-created arrays") \
  << help_entry( \
    "--java-cp-include-files r", \
    "regexp or JSON list of files to load (with '@' prefix)") \
  << help_entry( \
    "--java-load-class CLASS", \
    "also load code from class CLASS") \
  << help_entry( \
    "--java-no-load-class_CLASS", \
    "never load code from class CLASS") \
  << help_entry( \
    "--ignore-manifest-main-class", \
    "ignore Main-Class entries in JAR manifest files. If this option is " \
    "specified and the options --function and --main-class are not, we can " \
    "be certain that all classes in the JAR file are loaded.") \
  << help_entry( \
    "--context-include i", \
    "only analyze code matching specification i that") \
  << help_entry( \
    "--context-exclude e", \
    "does not match specification e. All other methods are excluded, i.e. we " \
    "load their signatures and meta-information, but not their bodies. A " \
    "specification is any prefix of a package, class or method name, e.g. " \
    "\"org.cprover.\" or \"org.cprover.MyClass.\" or " \
    "\"org.cprover.MyClass.methodToStub:(I)Z\". These options can be given " \
    "multiple times. The default for context-include is 'all included'; " \
    "default for context-exclude is 'nothing excluded'.") \
  << help_entry( \
    "--no-lazy-methods", \
    "load and translate all methods given on the command line and in " \
    "--classpath. Default is to load methods that appear to be reachable " \
    "from the --function entry point or main class Note that " \
    "--show-symbol-table, --show-goto-functions and --show-properties output " \
    "are restricted to loaded methods by default.") \
  << help_entry( \
    "--lazy-methods-extra-entry-point METHODNAME", \
    "treat METHODNAME as a possible program entry point for the purpose of " \
    "lazy method loading METHODNAME can be a regex that will be matched " \
    "against all symbols. If missing a java:: prefix will be added. If no " \
    "descriptor is found, all overloads of a method will also be added.") \
  << help_entry( \
    "--static-values f", \
    "Load initial values of static fields from the given JSON file. We " \
    "assign static fields to these values instead of calling the normal " \
    "static initializer (clinit) method. The argument can be a relative or " \
    "absolute path to the file.") \
  << help_entry( \
    "--java-lift-clinit-calls", \
    "Lifts clinit calls in function bodies to the top of the function. This " \
    "may reduce the overall cost of static initialisation, but may be " \
    "unsound if there are cyclic dependencies between static initializers " \
    "due to potentially changing their order of execution, or if static " \
    "initializers have side-effects such as updating another class' static " \
    "field.") \

#ifdef _WIN32
  #define JAVA_CLASSPATH_SEPARATOR ";"
#else
  #define JAVA_CLASSPATH_SEPARATOR ":"
#endif

#define HELP_JAVA_CLASSPATH /* NOLINT(*) */ \
  help_entry( \
    "-classpath dirs/jars, -cp dirs/jars, --classpath dirs/jars", \
    "set class search path of directories and jar files to a " \
    JAVA_CLASSPATH_SEPARATOR "-separated list of directories and JAR " \
    "archives to search for class files") \
  << help_entry("--main-class class-name", "set the name of the main class")

#define HELP_JAVA_METHOD_NAME /* NOLINT(*) */ \
  help_entry( \
    "method-name", \
    "fully qualified name of method  used as entry point, e.g. " \
    "mypackage.Myclass.foo:(I)Z")

#define HELP_JAVA_CLASS_NAME /* NOLINT(*) */ \
  help_entry( \
    "class-name", \
    "name of class. The entry point is the method specified by --function, " \
    "or otherwise, the public static void main(String[]) method of the given " \
    "class.")

#define OPT_JAVA_JAR /* NOLINT(*) */ \
  "(jar):"

#define HELP_JAVA_JAR /* NOLINT(*) */ \
  help_entry( \
    "-jar jarfile", \
    "JAR file to be checked. The entry point is the method specified by " \
    "--function or otherwise, the public static void main(String[]) method " \
    "of the class specified by --main-class or the main class specified in " \
    "the JAR manifes (checked in this order).")

#define OPT_JAVA_GOTO_BINARY /* NOLINT(*) */ \
  "(gb):"

#define HELP_JAVA_GOTO_BINARY /* NOLINT(*) */ \
  help_entry( \
    "--gb goto-binary", \
    "goto-binary file to be checked. The entry point is the method specified " \
    "by --function, or otherwise, the public static void main(String[]) of " \
    "the class specified by --main-class (checked in this order).")
// clang-format on

enum lazy_methods_modet
{
  LAZY_METHODS_MODE_EAGER,
  LAZY_METHODS_MODE_CONTEXT_INSENSITIVE,
  LAZY_METHODS_MODE_EXTERNAL_DRIVER
};

/// Map classes to the symbols they declare but is only computed once it is
/// needed and the map is then kept.
/// Note that it only includes function and field symbols (and not for example,
/// local variables), these are produced in the convert-class phase.
/// Calling `get` before the symbol table is properly filled with these symbols,
/// would make later calls return an outdated map. The
/// lazy_class_to_declared_symbols_mapt would then need to be reinitialized.
/// Similarly if some transformation creates or deletes function or field
/// symbols in the symbol table, then the map would get out of date and would
/// need to be reinitialized.
class lazy_class_to_declared_symbols_mapt
{
public:
  lazy_class_to_declared_symbols_mapt() = default;

  std::unordered_multimap<irep_idt, symbolt> &
  get(const symbol_table_baset &symbol_table);

  void reinitialize();

private:
  bool initialized = false;
  std::unordered_multimap<irep_idt, symbolt> map;
};

struct java_bytecode_language_optionst
{
  java_bytecode_language_optionst(const optionst &options, messaget &log);

  java_bytecode_language_optionst() = default;

  /// assume inputs variables to be non-null
  bool assume_inputs_non_null = false;
  bool string_refinement_enabled = false;
  bool throw_runtime_exceptions = false;
  bool assert_uncaught_exceptions = false;
  bool throw_assertion_error = false;
  bool threading_support = false;
  bool nondet_static = false;
  bool ignore_manifest_main_class = false;

  /// Transform `athrow` bytecode instructions into `assert FALSE` followed
  /// by `assume FALSE`.
  bool assert_no_exceptions_thrown = false;

  /// max size for user code created arrays
  size_t max_user_array_length = 0;
  lazy_methods_modet lazy_methods_mode =
    lazy_methods_modet::LAZY_METHODS_MODE_EAGER;

  /// list of classes to force load even without reference from the entry point
  std::vector<irep_idt> java_load_classes;
  std::string java_cp_include_files;
  /// JSON which contains initial values of static fields (right
  /// after the static initializer of the class was run). This is read from the
  /// file specified by the --static-values command-line option.
  optionalt<json_objectt> static_values_json;

  /// List of classes to never load
  std::unordered_set<std::string> no_load_classes;

  std::vector<load_extra_methodst> extra_methods;

  /// If set, method bodies are only elaborated if they pass the filter.
  /// Methods that do not pass the filter are "excluded": their symbols will
  /// include all the meta-information that is available from the bytecode
  /// (parameter types, return type, accessibility etc.) but the value of the
  /// symbol (corresponding to the body of the method) will be replaced with the
  /// same kind of "return nondet null or instance of return type" body that we
  /// use for stubbed methods. The original method body will never be loaded.
  optionalt<prefix_filtert> method_context;

  /// Should we lift clinit calls in function bodies to the top? For example,
  /// turning `if(x) A.clinit() else B.clinit()` into
  /// `A.clinit(); B.clinit(); if(x) ...`
  bool should_lift_clinit_calls;

  /// If set then a JAR file has been given via the -jar option.
  optionalt<std::string> main_jar;
};

#define JAVA_CLASS_MODEL_SUFFIX "@class_model"

class java_bytecode_languaget:public languaget
{
public:
  void set_language_options(const optionst &) override;

  void set_message_handler(message_handlert &message_handler) override;

  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream) override;

  // This is an extension to languaget
  // required because parsing of Java programs can be initiated without
  // opening a file first or providing a path to a file
  // as dictated by \ref languaget.
  virtual bool parse();

  bool parse(
    std::istream &instream,
    const std::string &path) override;

  bool generate_support_functions(symbol_table_baset &symbol_table) override;

  bool
  typecheck(symbol_table_baset &context, const std::string &module) override;

  virtual bool final(symbol_table_baset &context) override;

  void show_parse(std::ostream &out) override;

  virtual ~java_bytecode_languaget();
  java_bytecode_languaget(
    std::unique_ptr<select_pointer_typet> pointer_type_selector)
    : object_factory_parameters(),
      pointer_type_selector(std::move(pointer_type_selector))
  {
  }

  java_bytecode_languaget():
    java_bytecode_languaget(
      std::unique_ptr<select_pointer_typet>(new select_pointer_typet()))
  {
  }

  bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns) override;

  bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns) override;

  bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    const namespacet &ns) override;

  std::unique_ptr<languaget> new_language() override
  { return util_make_unique<java_bytecode_languaget>(); }

  std::string id() const override { return "java"; }
  std::string description() const override { return "Java Bytecode"; }
  std::set<std::string> extensions() const override;

  void modules_provided(std::set<std::string> &modules) override;
  virtual void
  methods_provided(std::unordered_set<irep_idt> &methods) const override;
  virtual void convert_lazy_method(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table) override;

protected:
  void convert_single_method(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    lazy_class_to_declared_symbols_mapt &class_to_declared_symbols)
  {
    convert_single_method(
      function_id,
      symbol_table,
      optionalt<ci_lazy_methods_neededt>(),
      class_to_declared_symbols);
  }
  bool convert_single_method(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
    lazy_class_to_declared_symbols_mapt &class_to_declared_symbols);
  bool convert_single_method_code(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
    lazy_class_to_declared_symbols_mapt &class_to_declared_symbols);

  bool do_ci_lazy_method_conversion(symbol_table_baset &);
  const select_pointer_typet &get_pointer_type_selector() const;

  optionalt<java_bytecode_language_optionst> language_options;
  irep_idt main_class;
  std::vector<irep_idt> main_jar_classes;
  java_class_loadert java_class_loader;
  java_object_factory_parameterst object_factory_parameters;
  method_bytecodet method_bytecode;
  java_string_library_preprocesst string_preprocess;

private:
  virtual std::vector<load_extra_methodst>
  build_extra_entry_points(const optionst &) const;
  const std::unique_ptr<const select_pointer_typet> pointer_type_selector;

  /// Maps synthetic method names on to the particular type of synthetic method
  /// (static initializer, initializer wrapper, etc). For full documentation see
  /// synthetic_method_map.h
  synthetic_methods_mapt synthetic_methods;
  stub_global_initializer_factoryt stub_global_initializer_factory;
  class_hierarchyt class_hierarchy;

  /// Map used in all calls to functions that deterministically create objects
  /// (currently only \ref assign_from_json).
  /// It tracks objects that should be reference-equal to each other by mapping
  /// IDs of such objects to symbols that store their values.
  std::unordered_map<std::string, object_creation_referencet> references;

  void parse_from_main_class();
  void initialize_class_loader();
};

std::unique_ptr<languaget> new_java_bytecode_language();

void parse_java_language_options(const cmdlinet &cmd, optionst &options);

prefix_filtert get_context(const optionst &options);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
