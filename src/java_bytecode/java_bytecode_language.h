/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H

#include <util/language.h>
#include <util/cmdline.h>

#include "java_class_loader.h"
#include "java_string_library_preprocess.h"

#define MAX_NONDET_ARRAY_LENGTH_DEFAULT 5

class symbolt;

enum lazy_methods_modet
{
  LAZY_METHODS_MODE_EAGER,
  LAZY_METHODS_MODE_CONTEXT_INSENSITIVE,
  LAZY_METHODS_MODE_CONTEXT_SENSITIVE
};

typedef std::pair<
          const symbolt *,
          const java_bytecode_parse_treet::methodt *>
  lazy_method_valuet;
typedef std::map<irep_idt, lazy_method_valuet>
  lazy_methodst;

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

  bool typecheck(
    symbol_tablet &context,
    const std::string &module) override;

  void replace_string_methods(symbol_tablet &context);

  virtual bool final(
    symbol_tablet &context) override;

  void show_parse(std::ostream &out) override;

  virtual ~java_bytecode_languaget();
  java_bytecode_languaget():
    max_nondet_array_length(MAX_NONDET_ARRAY_LENGTH_DEFAULT),
    max_user_array_length(0)
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

  languaget *new_language() override
  { return new java_bytecode_languaget; }

  std::string id() const override { return "java"; }
  std::string description() const override { return "Java Bytecode"; }
  std::set<std::string> extensions() const override;

  void modules_provided(std::set<std::string> &modules) override;
  virtual void lazy_methods_provided(std::set<irep_idt> &) const override;
  virtual void convert_lazy_method(
    const irep_idt &id, symbol_tablet &) override;

protected:
  bool do_ci_lazy_method_conversion(symbol_tablet &, lazy_methodst &);

  irep_idt main_class;
  std::vector<irep_idt> main_jar_classes;
  java_class_loadert java_class_loader;
  bool assume_inputs_non_null;      // assume inputs variables to be non-null
  size_t max_nondet_array_length;   // maximal length for non-det array creation
  size_t max_user_array_length;     // max size for user code created arrays
  lazy_methodst lazy_methods;
  lazy_methods_modet lazy_methods_mode;
  bool string_refinement_enabled;
  bool throw_runtime_exceptions;
  java_string_library_preprocesst string_preprocess;
  std::string java_cp_include_files;
};

languaget *new_java_bytecode_language();

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
