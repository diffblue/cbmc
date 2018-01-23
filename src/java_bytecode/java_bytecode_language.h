/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H

#include <memory>

#include <util/language.h>
#include <util/cmdline.h>
#include <util/make_unique.h>

#include "ci_lazy_methods.h"
#include "ci_lazy_methods_needed.h"
#include "java_class_loader.h"
#include "java_string_library_preprocess.h"

#include <java_bytecode/select_pointer_type.h>

#define JAVA_BYTECODE_LANGUAGE_OPTIONS /*NOLINT*/                              \
  "(java-assume-inputs-non-null)"                                              \
  "(java-throw-runtime-exceptions)"                                            \
  "(java-max-input-array-length):"                                             \
  "(java-max-input-tree-depth):"                                               \
  "(java-max-vla-length):"                                                     \
  "(java-cp-include-files):"                                                   \
  "(lazy-methods)"                                                             \
  "(lazy-methods-extra-entry-point):"                                          \
  "(java-load-class):"

#define JAVA_BYTECODE_LANGUAGE_OPTIONS_HELP /*NOLINT*/                                          \
  " --java-assume-inputs-non-null    never initialize reference-typed parameter to the\n"       \
  "                                  entry point with null\n"                                   \
  " --java-throw-runtime-exceptions  make implicit runtime exceptions explicit\n"               \
  " --java-max-input-array-length N  limit input array size to <= N\n"                          \
  " --java-max-input-tree-depth N    object references are (deterministically) set to null in\n"\
  "                                  the object\n"                                              \
  " --java-max-vla-length            limit the length of user-code-created arrays\n"            \
  " --java-cp-include-files          regexp or JSON list of files to load (with '@' prefix)\n"  \
  " --lazy-methods                   only translate methods that appear to be reachable from\n" \
  "                                  the --function entry point or main class\n"                \
  " --lazy-methods-extra-entry-point METHODNAME\n"                                              \
  "                                  treat METHODNAME as a possible program entry point for\n"  \
  "                                  the purpose of lazy method loading\n"                      \
  "                                  A '.*' wildcard is allowed to specify all class members\n"

#define MAX_NONDET_ARRAY_LENGTH_DEFAULT 5
#define MAX_NONDET_STRING_LENGTH std::numeric_limits<std::int32_t>::max()
#define MAX_NONDET_TREE_DEPTH 5

class symbolt;

enum lazy_methods_modet
{
  LAZY_METHODS_MODE_EAGER,
  LAZY_METHODS_MODE_CONTEXT_INSENSITIVE,
  LAZY_METHODS_MODE_CONTEXT_SENSITIVE
};

struct object_factory_parameterst final
{
  /// Maximum value for the non-deterministically-chosen length of an array.
  size_t max_nondet_array_length=MAX_NONDET_ARRAY_LENGTH_DEFAULT;

  /// Maximum value for the non-deterministically-chosen length of a string.
  size_t max_nondet_string_length=MAX_NONDET_STRING_LENGTH;

  /// Maximum depth for object hierarchy on input.
  /// Used to prevent object factory to loop infinitely during the
  /// generation of code that allocates/initializes data structures of recursive
  /// data types or unbounded depth. We bound the maximum number of times we
  /// dereference a pointer using a 'depth counter'. We set a pointer to null if
  /// such depth becomes >= than this maximum value.
  size_t max_nondet_tree_depth=MAX_NONDET_TREE_DEPTH;

  /// Force string content to be ASCII printable characters when set to true.
  bool string_printable = false;
};

class java_bytecode_languaget:public languaget
{
public:
  virtual void get_language_options(const cmdlinet &) override;

  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream) override;

  bool parse(
    std::istream &instream,
    const std::string &path) override;

  bool generate_support_functions(
    symbol_tablet &symbol_table) override;

  bool typecheck(
    symbol_tablet &context,
    const std::string &module) override;

  virtual bool final(symbol_table_baset &context) override;

  void show_parse(std::ostream &out) override;

  virtual ~java_bytecode_languaget();
  java_bytecode_languaget(
    std::unique_ptr<select_pointer_typet> pointer_type_selector):
      assume_inputs_non_null(false),
      object_factory_parameters(),
      max_user_array_length(0),
      lazy_methods_mode(lazy_methods_modet::LAZY_METHODS_MODE_EAGER),
      string_refinement_enabled(false),
      pointer_type_selector(std::move(pointer_type_selector))
  {}

  java_bytecode_languaget():
    java_bytecode_languaget(
      std::unique_ptr<select_pointer_typet>(new select_pointer_typet()))
  {}


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
  virtual void methods_provided(id_sett &methods) const override;
  virtual void convert_lazy_method(
    const irep_idt &function_id,
    symbol_tablet &symbol_table) override;

protected:
  void convert_single_method(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table)
  {
    convert_single_method(
      function_id, symbol_table, optionalt<ci_lazy_methods_neededt>());
  }
  bool convert_single_method(
    const irep_idt &function_id,
    symbol_table_baset &symbol_table,
    optionalt<ci_lazy_methods_neededt> needed_lazy_methods);

  bool do_ci_lazy_method_conversion(symbol_tablet &, method_bytecodet &);
  const select_pointer_typet &get_pointer_type_selector() const;

  irep_idt main_class;
  std::vector<irep_idt> main_jar_classes;
  java_class_loadert java_class_loader;
  bool assume_inputs_non_null;      // assume inputs variables to be non-null
  object_factory_parameterst object_factory_parameters;
  size_t max_user_array_length;     // max size for user code created arrays
  method_bytecodet method_bytecode;
  lazy_methods_modet lazy_methods_mode;
  std::vector<irep_idt> lazy_methods_extra_entry_points;
  bool string_refinement_enabled;
  bool throw_runtime_exceptions;
  java_string_library_preprocesst string_preprocess;
  std::string java_cp_include_files;

  // list of classes to force load even without reference from the entry point
  std::vector<irep_idt> java_load_classes;

private:
  /// Should be overridden by driver programs that will provide stub methods,
  /// i.e. they pledge to replace any function that cannot be elaborated here
  /// with some function body.
  virtual bool driver_program_provides_stubs() { return false; }

  const std::unique_ptr<const select_pointer_typet> pointer_type_selector;
};

std::unique_ptr<languaget> new_java_bytecode_language();

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
