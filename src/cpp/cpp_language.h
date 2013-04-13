/*******************************************************************\

Module: C++ Language Module

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_LANGUAGE_H
#define CPROVER_CPP_LANGUAGE_H

/*! \defgroup gr_cpp C++ front-end */

#include <util/language.h>

#include "cpp_parse_tree.h"

/*! \brief TO_BE_DOCUMENTED
    \ingroup gr_cpp
*/
class cpp_languaget:public languaget
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
    symbol_tablet &symbol_table,
    const std::string &module,
    message_handlert &message_handler);

  bool merge_symbol_table(
    symbol_tablet &dest,
    symbol_tablet &src,
    message_handlert &message_handler,
    const std::string &module,
    class replace_symbolt &replace_symbol) const; 

  virtual bool final(
    symbol_tablet &symbol_table,
    message_handlert &message_handler);

  virtual void show_parse(std::ostream &out);

  // constructor, destructor
  virtual ~cpp_languaget();
  cpp_languaget() { }

  // conversion from expression into string
  virtual bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns);

  // conversion from type into string
  virtual bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns);

  // conversion from string into expression
  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    message_handlert &message_handler,
    const namespacet &ns);

  virtual languaget *new_language()
  { return new cpp_languaget; }

  virtual std::string id() const { return "cpp"; }
  virtual std::string description() const { return "C++"; }
  virtual std::set<std::string> extensions() const;

  virtual void modules_provided(std::set<std::string> &modules);

protected:
  cpp_parse_treet cpp_parse_tree;
  std::string parse_path;

  void show_parse(std::ostream &out, const cpp_itemt &item);

  virtual std::string main_symbol()
  {
    return "c::main";
  }
};

languaget *new_cpp_language();

#endif
