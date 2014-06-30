/*******************************************************************\

Module: Abstract interface to support a programming language

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LANGUAGE_H
#define CPROVER_LANGUAGE_H

#include <set>
#include <iosfwd>
#include <string>

#include "message.h"

class symbol_tablet;
class exprt;
class namespacet;
class typet;

class languaget:public messaget
{
public:
  // parse file
  
  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream) { return false; }
  
  virtual bool parse(
    std::istream &instream,
    const std::string &path)=0;
  
  // add external dependencies of a given module to set
  
  virtual void dependencies(
    const std::string &module,
    std::set<std::string> &modules);

  // add modules provided by currently parsed file to set

  virtual void modules_provided(std::set<std::string> &modules)
  { }

  // final adjustments, e.g., initialization and call to main()

  virtual bool final(
    symbol_tablet &symbol_table);

  // type check interfaces of currently parsed file

  virtual bool interfaces(
    symbol_tablet &symbol_table);

  // type check a module in the currently parsed file

  virtual bool typecheck(
    symbol_tablet &symbol_table,
    const std::string &module)=0;
  
  // language id / description
  
  virtual std::string id() const { return ""; }
  virtual std::string description() const { return ""; }
  virtual std::set<std::string> extensions() const
  { return std::set<std::string>(); }
  
  // show parse tree

  virtual void show_parse(std::ostream &out)=0;
             
  // conversion of expressions
  
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
    const namespacet &ns)=0;
                       
  virtual languaget *new_language()=0;
  
  // constructor / destructor
  
  languaget() { }
  virtual ~languaget() { }
};
#endif
