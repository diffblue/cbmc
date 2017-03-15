/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <memory>

#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/language.h>
#include <util/std_expr.h>

#include "pretty_printer.h"
#include "language_util.h"
#include "mode.h"

/*******************************************************************\

Function: get_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static languaget* get_language(
  const namespacet &ns,
  const irep_idt &identifier)
{
  const symbolt *symbol;

  if(identifier=="" ||
     ns.lookup(identifier, symbol) ||
     symbol->mode=="")
    return get_default_language();

  languaget *ptr=get_language_from_mode(symbol->mode);

  if(ptr==NULL)
    throw "symbol `"+id2string(symbol->name)+
      "' has unknown mode '"+id2string(symbol->mode)+"'";

  return ptr;
}

std::vector<pretty_printer_factoryt> registered_pretty_printers;

void register_global_pretty_printer(pretty_printer_factoryt new_printer)
{
  registered_pretty_printers.push_back(new_printer);
}

static std::vector<std::unique_ptr<pretty_printert>> get_pretty_printer_stack(
  const namespacet &ns,
  std::unique_ptr<pretty_printert> language_printer)
{
  std::vector<std::unique_ptr<pretty_printert>> ret;
  ret.push_back(std::unique_ptr<pretty_printert>(new norep_pretty_printert()));
  for(const auto &factory : registered_pretty_printers)
    ret.push_back(factory(ns));
  ret.push_back(std::move(language_printer));

  // Link the printers together (used for deferral of expressions
  // a particular printer can't handle)
  for(std::size_t i=0; i<ret.size()-1; ++i)
    ret[i+1]->set_next_pretty_printer(ret[i].get());

  // Give all printers in the chain a pointer to the top, for use
  // printing subexpressions that others should have a chance
  // to handle:
  for(std::size_t i=0; i<ret.size(); ++i)
    ret[i]->set_top_pretty_printer(ret.back().get());

  return ret;
}

/*******************************************************************\

Function: from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr)
{
  std::unique_ptr<languaget> p(get_language(ns, identifier));
  auto printers=get_pretty_printer_stack(ns, p->get_pretty_printer(ns));
  return printers.back()->convert(expr);
}

/*******************************************************************\

Function: from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string from_type(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p(get_language(ns, identifier));
  auto printers=get_pretty_printer_stack(ns, p->get_pretty_printer(ns));
  return printers.back()->convert(type);
}

/*******************************************************************\

Function: type_to_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type_to_name(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p(get_language(ns, identifier));

  std::string result;
  p->type_to_name(type, result, ns);

  return result;
}

/*******************************************************************\

Function: from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string from_expr(const exprt &expr)
{
  symbol_tablet symbol_table;
  return from_expr(namespacet(symbol_table), "", expr);
}

/*******************************************************************\

Function: from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string from_type(const typet &type)
{
  symbol_tablet symbol_table;
  return from_type(namespacet(symbol_table), "", type);
}

/*******************************************************************\

Function: to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt to_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const std::string &src)
{
  std::unique_ptr<languaget> p(get_language(ns, identifier));

  const symbolt &symbol=ns.lookup(identifier);

  exprt expr;

  if(p->to_expr(src, id2string(symbol.module), expr, ns))
    return nil_exprt();

  return expr;
}

/*******************************************************************\

Function: type_to_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string type_to_name(const typet &type)
{
  symbol_tablet symbol_table;
  return type_to_name(namespacet(symbol_table), "", type);
}
