/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_LANGUAGE_H
#define CPROVER_JAVA_BYTECODE_LANGUAGE_H

#include <util/language.h>

#include "java_bytecode_parse_tree.h"

class java_bytecode_languaget:public languaget
{
public:
  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream,
    message_handlert &message_handler);

  virtual bool parse(
    std::istream &instream,
    const std::string &path,
    message_handlert &message_handler);
             
  virtual bool typecheck(
    symbol_tablet &context,
    const std::string &module,
    message_handlert &message_handler);

  virtual bool final(
    symbol_tablet &context,
    message_handlert &message_handler);

  virtual void show_parse(std::ostream &out);
  
  virtual ~java_bytecode_languaget();
  java_bytecode_languaget() { }
  
  virtual bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns);

  virtual bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns);

  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    message_handlert &message_handler,
    const namespacet &ns);
                       
  virtual languaget *new_language()
  { return new java_bytecode_languaget; }
   
  virtual std::string id() const { return "java"; }
  virtual std::string description() const { return "Java Bytecode"; }
  virtual std::set<std::string> extensions() const;

  virtual void modules_provided(std::set<std::string> &modules);  
  
protected:
  java_bytecode_parse_treet parse_tree;
  std::string parse_path;
};
 
languaget *new_java_bytecode_language();
 
#endif
