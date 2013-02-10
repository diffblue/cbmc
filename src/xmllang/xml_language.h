/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_XML_LANGUAGE_H
#define CPROVER_XML_LANGUAGE_H

#include <language.h>

#include "xml_parse_tree.h"

class xml_languaget:public languaget
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

  virtual bool final(
    symbol_tablet &symbol_table,
    message_handlert &message_handler);

  virtual void show_parse(std::ostream &out);
  
  virtual ~xml_languaget();
  xml_languaget() { }
  
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
  { return new xml_languaget; }
   
  virtual std::string id() const { return "xml"; }
  virtual std::string description() const { return "XML"; }
  virtual std::set<std::string> extensions() const
  { std::set<std::string> s; s.insert("xml"); return s; }

  virtual void modules_provided(std::set<std::string> &modules);
  
protected:
  xml_parse_treet xml_parse_tree;
  
  std::string parse_path;
};
 
languaget *new_xml_language();
 
#endif
