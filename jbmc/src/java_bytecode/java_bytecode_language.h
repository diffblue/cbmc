/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H

#include <util/json.h>
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

#define JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP \
  " {y--disable-uncaught-exception-check} \t " \
  "ignore uncaught exceptions and errors\n" \
  " {y--throw-assertion-error} \t " \
  "throw java.lang.AssertionError on violated assert statements instead of " \
  "failing at the location of the assert statement\n" \
  " {y--throw-runtime-exceptions} \t " \
  "make implicit runtime exceptions explicit\n" \
  " {y--assert-no-exceptions-thrown} \t " \
  "transform `throw` instructions into `assert FALSE` followed by " \
  "`assume FALSE`.\n" \
  " {y--max-nondet-array-length} {uN} \t " \
  "limit nondet (e.g. input) array size to <= {uN}\n" \
  " {y--max-nondet-tree-depth} {uN} \t " \
  "limit size of nondet (e.g. input) object tree; at level {uN} references " \
  "are set to null\n" \
  " {y--java-assume-inputs-non-null} \t " \
  "never initialize reference-typed parameter to the entry point with null\n" \
  " {y--java-assume-inputs-interval} {y[}{uL}{y:}{uU}|{uL}{y:}|{y:}{uU}{y]} " \
  "\t " \
  "force numerical primitive-typed inputs (byte, short, int, long, float, " \
  "double) to be initialized within the given range; lower bound {uL} and " \
  "upper bound {uU} must be integers; does not work for arrays\n" \
  " {y--java-assume-inputs-integral} \t " \
  "force float and double inputs to have integer values; does not work for " \
  "arrays\n" \
  " {y--java-max-vla-length} {uN} \t " \
  "limit the length of user-code-created arrays\n" \
  " {y--java-cp-include-files} {ur} \t " \
  "regexp or JSON list of files to load (with '@' prefix)\n" \
  " {y--java-load-class} {uCLASS} \t also load code from class {uCLASS}\n" \
  " {y--java-no-load-class} {uCLASS} \t never load code from class " \
  "{uCLASS}\n" \
  " {y--ignore-manifest-main-class} \t " \
  "ignore Main-Class entries in JAR manifest files. If this option is " \
  "specified and the options {y--function} and {y--main-class} are not, we " \
  "can be certain that all classes in the JAR file are loaded.\n" \
  " {y--context-include} {ui} \t " \
  "only analyze code matching specification {ui}\n" \
  " {y--context-exclude} {ue} \t " \
  "only analyze code does not match specification {ue}. All other methods " \
  "are excluded, i.e. we load their signatures and meta-information, but not " \
  "their bodies. A specification is any prefix of a package, class or method " \
  "name, e.g. \"org.cprover.\" or \"org.cprover.MyClass.\" or " \
  "\"org.cprover.MyClass.methodToStub:(I)Z\". These options can be given " \
  "multiple times. The default for context-include is 'all included'; " \
  "default for context-exclude is 'nothing excluded'.\n" \
  " {y--no-lazy-methods} \t " \
  "load and translate all methods given on the command line and in " \
  "{y--classpath}. Default is to load methods that appear to be reachable " \
  "from the {y--function} entry point or main class Note that " \
  "{y--show-symbol-table}, {y--show-goto-functions} and " \
  "{y--show-properties} output are restricted to loaded methods by default.\n" \
  " {y--lazy-methods-extra-entry-point} {uMETHODNAME} \t " \
  "treat {uMETHODNAME} as a possible program entry point for the purpose of " \
  "lazy method loading {uMETHODNAME} can be a regex that will be matched " \
  "against all symbols. If missing a java:: prefix will be added. If no " \
  "descriptor is found, all overloads of a method will also be added.\n" \
  " {y--static-values} {uf} \t " \
  "Load initial values of static fields from the given JSON file {uf}. We " \
  "assign static fields to these values instead of calling the normal " \
  "static initializer (clinit) method. The argument can be a relative or " \
  "absolute path to the file.\n" \
  " {y--java-lift-clinit-calls} \t " \
  "Lifts clinit calls in function bodies to the top of the function. This " \
  "may reduce the overall cost of static initialisation, but may be unsound " \
  "if there are cyclic dependencies between static initializers due to " \
  "potentially changing their order of execution, or if static initializers " \
  "have side-effects such as updating another class' static field.\n" \

#ifdef _WIN32
  #define JAVA_CLASSPATH_SEPARATOR ";"
#else
  #define JAVA_CLASSPATH_SEPARATOR ":"
#endif

#define HELP_JAVA_CLASSPATH \
  " {y-classpath} {udirs/jars}, {y-cp} {udirs/jars}, " \
  "{y--classpath} {udirs/jars} \t " \
  "set class search path of directories and jar files to a " \
  JAVA_CLASSPATH_SEPARATOR "-separated list of directories and JAR " \
  "archives to search for class files\n" \
  " {y--main-class} {uclass-name} \t set the name of the main class\n"

#define HELP_JAVA_METHOD_NAME \
  "  {umethod-name} \t " \
  "fully qualified name of method  used as entry point, e.g. " \
  "mypackage.Myclass.foo:(I)Z\n"

#define HELP_JAVA_CLASS_NAME \
  "  {uclass-name} \t " \
  "name of class. The entry point is the method specified by --function, " \
  "or otherwise, the public static void main(String[]) method of the given " \
  "class.\n"

#define OPT_JAVA_JAR \
  "(jar):"

#define HELP_JAVA_JAR \
  " {y-jar} {ujarfile} \t " \
  "JAR file to be checked. The entry point is the method specified by " \
  "{y--function} or otherwise, the public static void main(String[]) method " \
  "of the class specified by {y--main-class} or the main class specified in " \
  "the JAR manifest (checked in this order).\n"

#define OPT_JAVA_GOTO_BINARY \
  "(gb):"

#define HELP_JAVA_GOTO_BINARY \
  " {y--gb} {ugoto-binary} \t " \
  "goto-binary file to be checked. The entry point is the method specified " \
  "by {y--function}, or otherwise, the public static void main(String[]) of " \
  "the class specified by {y--main-class} (checked in this order).\n"
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
  java_bytecode_language_optionst(const optionst &options, message_handlert &);

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
  std::optional<json_objectt> static_values_json;

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
  std::optional<prefix_filtert> method_context;

  /// Should we lift clinit calls in function bodies to the top? For example,
  /// turning `if(x) A.clinit() else B.clinit()` into
  /// `A.clinit(); B.clinit(); if(x) ...`
  bool should_lift_clinit_calls;

  /// If set then a JAR file has been given via the -jar option.
  std::optional<std::string> main_jar;
};

#define JAVA_CLASS_MODEL_SUFFIX "@class_model"

class java_bytecode_languaget:public languaget
{
public:
  void set_language_options(const optionst &, message_handlert &) override;

  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream,
    message_handlert &message_handler) override;

  bool parse(
    std::istream &instream,
    const std::string &path,
    message_handlert &message_handler) override;

  bool generate_support_functions(
    symbol_table_baset &symbol_table,
    message_handlert &message_handler) override;

  bool typecheck(
    symbol_table_baset &context,
    const std::string &module,
    message_handlert &message_handler) override;

  virtual bool final(symbol_table_baset &context) override;

  void show_parse(std::ostream &out, message_handlert &) override;

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
    const namespacet &ns,
    message_handlert &message_handler) override;

  std::unique_ptr<languaget> new_language() override
  {
    return std::make_unique<java_bytecode_languaget>();
  }

  std::string id() const override { return "java"; }
  std::string description() const override { return "Java Bytecode"; }
  std::set<std::string> extensions() const override;

  void modules_provided(std::set<std::string> &modules) override;
  virtual void
  methods_provided(std::unordered_set<irep_idt> &methods) const override;
  virtual void convert_lazy_method(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    message_handlert &message_handler) override;

protected:
  void convert_single_method(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    lazy_class_to_declared_symbols_mapt &class_to_declared_symbols,
    message_handlert &message_handler)
  {
    convert_single_method(
      function_id,
      symbol_table,
      std::optional<ci_lazy_methods_neededt>(),
      class_to_declared_symbols,
      message_handler);
  }
  bool convert_single_method(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    std::optional<ci_lazy_methods_neededt> needed_lazy_methods,
    lazy_class_to_declared_symbols_mapt &class_to_declared_symbols,
    message_handlert &);
  bool convert_single_method_code(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    std::optional<ci_lazy_methods_neededt> needed_lazy_methods,
    lazy_class_to_declared_symbols_mapt &class_to_declared_symbols,
    message_handlert &);

  bool do_ci_lazy_method_conversion(symbol_table_baset &, message_handlert &);
  const select_pointer_typet &get_pointer_type_selector() const;

  std::optional<java_bytecode_language_optionst> language_options;
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

  void parse_from_main_class(message_handlert &);
  void initialize_class_loader(message_handlert &);
};

std::unique_ptr<languaget> new_java_bytecode_language();

void parse_java_language_options(const cmdlinet &cmd, optionst &options);

prefix_filtert get_context(const optionst &options);

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
