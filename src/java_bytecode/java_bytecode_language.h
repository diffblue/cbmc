/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H

#include <util/language.h>
#include <util/cmdline.h>

#include "java_class_loader.h"

#define MAX_NONDET_ARRAY_LENGTH_DEFAULT 5

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

  bool final(
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

  virtual bool generate_start_function(
    const class symbolt &entry_function_symbol,
    class symbol_tablet &symbol_table) override;

protected:
  irep_idt main_class;
  java_class_loadert java_class_loader;
  bool assume_inputs_non_null;      // assume inputs variables to be non-null

  bool disable_runtime_checks;      // disable run-time checks for java, i.e.,
                                    // ASSERTS for
                                    //  - checkcast / instanceof
                                    //  - array bounds check
                                    //  - array size for newarray
  size_t max_nondet_array_length;   // maximal length for non-det array creation
  size_t max_user_array_length;     // max size for user code created arrays
};

languaget *new_java_bytecode_language();

#endif // CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_LANGUAGE_H
