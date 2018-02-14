/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H

#include <memory>

#include <util/cmdline.h>
#include <util/make_unique.h>

#include <langapi/language.h>

#include "ci_lazy_methods.h"
#include "ci_lazy_methods_needed.h"
#include "java_class_loader.h"
#include "java_static_initializers.h"
#include "java_string_library_preprocess.h"
#include "object_factory_parameters.h"
#include "synthetic_methods_map.h"

#include <java_bytecode/select_pointer_type.h>

#define JAVA_BYTECODE_LANGUAGE_OPTIONS /*NOLINT*/                              \
  "(no-core-models)"                                                           \
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
  " --no-core-models                 don't load internally provided models for core classes in\n"/* NOLINT(*) */ \
  "                                  the Java Class Library\n"                                   /* NOLINT(*) */ \
  " --java-assume-inputs-non-null    never initialize reference-typed parameter to the\n"        /* NOLINT(*) */ \
  "                                  entry point with null\n"                                    /* NOLINT(*) */ \
  " --java-throw-runtime-exceptions  make implicit runtime exceptions explicit\n"                /* NOLINT(*) */ \
  " --java-max-input-array-length N  limit input array size to <= N\n"                           /* NOLINT(*) */ \
  " --java-max-input-tree-depth N    object references are (deterministically) set to null in\n" /* NOLINT(*) */ \
  "                                  the object\n"                                               /* NOLINT(*) */ \
  " --java-max-vla-length            limit the length of user-code-created arrays\n"             /* NOLINT(*) */ \
  " --java-cp-include-files          regexp or JSON list of files to load (with '@' prefix)\n"   /* NOLINT(*) */ \
  " --lazy-methods                   only translate methods that appear to be reachable from\n"  /* NOLINT(*) */ \
  "                                  the --function entry point or main class\n"                 /* NOLINT(*) */ \
  " --lazy-methods-extra-entry-point METHODNAME\n"                                               /* NOLINT(*) */ \
  "                                  treat METHODNAME as a possible program entry point for\n"   /* NOLINT(*) */ \
  "                                  the purpose of lazy method loading\n"                       /* NOLINT(*) */ \
  "                                  A '.*' wildcard is allowed to specify all class members\n"

class symbolt;

enum lazy_methods_modet
{
  LAZY_METHODS_MODE_EAGER,
  LAZY_METHODS_MODE_CONTEXT_INSENSITIVE,
  LAZY_METHODS_MODE_CONTEXT_SENSITIVE
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
    symbol_table_baset &symbol_table) override;

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
  const std::unique_ptr<const select_pointer_typet> pointer_type_selector;
  synthetic_methods_mapt synthetic_methods;
  stub_global_initializer_factoryt stub_global_initializer_factory;
  class_hierarchyt class_hierarchy;
};

std::unique_ptr<languaget> new_java_bytecode_language();

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
