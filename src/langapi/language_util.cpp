// Copyright 2016-2017 DiffBlue Limited. All Rights Reserved.


#include "language_util.h"

#include <memory>

#include <util/symbol_table.h>
#include <util/namespace.h>
#include <util/language.h>
#include <util/std_expr.h>

#include "pretty_printer.h"
#include "mode.h"

static std::unique_ptr<languaget> get_language(
  const namespacet &ns,
  const irep_idt &identifier)
{
  const symbolt *symbol;

  if(identifier=="" ||
     ns.lookup(identifier, symbol) ||
     symbol->mode=="")
    return get_default_language();

  std::unique_ptr<languaget> ptr=get_language_from_mode(symbol->mode);

  if(ptr==nullptr)
    throw "symbol `"+id2string(symbol->name)+
      "' has unknown mode '"+id2string(symbol->mode)+"'";

  return ptr;
}

std::vector<pretty_printer_factoryt> registered_pretty_printers;

/// This registers a custom pretty-printer for use printing expressions with
/// `from_expr` and `from_type` also defined in language_util.h. The function
/// given should allocate an instance of the printer and return a unique_ptr
/// that disposes of it appropriately (so if allocated with `new`, ordinary
/// `std::unique_ptr` will do the trick). `from_expr` and `from_type` will
/// always build a stack of printer classes of the form: L -> C1 -> C2 ... Cn ->
/// X
///
///          L is the language frontend pretty-printer associated
///          with an expression, C1 ... Cn are instances of the registered
///          custom printers in order of registration, and X is the fallback
///          irep-to-lisp printer `norep_pretty_printert`. The -> arrows
///          represent `next_pretty_printer` fields used to defer printing
///          of expressions a particular printer can't handle; all printers
///          in the stack also get `top_pretty_printer` set to point at L,
///          which they should use when printing subexpressions to give
///          the whole stack a chance to provide a representation.
///
///          Note at present language custom printers such as `expr2javat`
///          are subclasses of `expr2ct` rather than using this deferral
///          mechanism; thus even when a Java expression is being printed
///          there is still only one L in the stack, rather than
///          expr2javat -> expr2ct -> C1 ... Cn -> X
///          as one might expect. The language printers (in particular
///          expr2ct) always assume they are at the top of the stack
///          (so top_pretty_printer == this), and will need adapting if
///          we want to e.g. place a custom printer *above* expr2ct
///          in the future.
/// \param `new_printer`: factory method returning `unique_ptr<pretty_printert>`
void register_global_pretty_printer(pretty_printer_factoryt new_printer)
{
  registered_pretty_printers.push_back(new_printer);
}

/// (See `register_global_pretty_printer` above for context) Takes a reference
/// to language-specific pretty-printer L, instantiates custom printers C1 .. Cn
/// if any have been registered, creates the fallback norep pretty-printer X,
/// and sets their next_ and top_pretty_printer pointers. A vector of unique
/// pointers is returned whose back member is the head of the stack (L, in the
/// notation used above).
/// \param `ns`: namespace
/// \param `language_printer`: pointer to instance of a pretty-printer that
///   should be placed at the head of the printer stack.
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

/// Pretty-prints an expression. If custom pretty-printers have been registered
/// they will be instantiated and may take part in printing `expr`; see
/// `register_global_pretty_printer` for details.
/// \param `ns`: global namespace
/// \param `identifier`: symbol-table identifier associated with `expr` or the
///   empty string if none
/// \param `expr`: expression to print
/// \return Returns pretty-printed string equivalent of `expr`.
std::string from_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr)
{
  std::unique_ptr<languaget> p(get_language(ns, identifier));
  auto printers=get_pretty_printer_stack(ns, p->get_pretty_printer(ns));
  return printers.back()->convert(expr);
}

/// Pretty-prints an type. If custom pretty-printers have been registered they
/// will be instantiated and may take part in printing `type`; see
/// `register_global_pretty_printer` for details.
/// \param `ns`: global namespace
/// \param `identifier`: symbol-table identifier associated with `type` or the
///   empty string if none
/// \param `type`: type to print
/// \return Returns pretty-printed string equivalent of `type`.
std::string from_type(
  const namespacet &ns,
  const irep_idt &identifier,
  const typet &type)
{
  std::unique_ptr<languaget> p(get_language(ns, identifier));
  auto printers=get_pretty_printer_stack(ns, p->get_pretty_printer(ns));
  return printers.back()->convert(type);
}

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

std::string from_expr(const exprt &expr)
{
  symbol_tablet symbol_table;
  return from_expr(namespacet(symbol_table), "", expr);
}

std::string from_type(const typet &type)
{
  symbol_tablet symbol_table;
  return from_type(namespacet(symbol_table), "", type);
}

exprt to_expr(
  const namespacet &ns,
  const irep_idt &identifier,
  const std::string &src)
{
  std::unique_ptr<languaget> p(get_language(ns, identifier));

  null_message_handlert null_message_handler;
  p->set_message_handler(null_message_handler);

  const symbolt &symbol=ns.lookup(identifier);

  exprt expr;

  if(p->to_expr(src, id2string(symbol.module), expr, ns))
    return nil_exprt();

  return expr;
}

std::string type_to_name(const typet &type)
{
  symbol_tablet symbol_table;
  return type_to_name(namespacet(symbol_table), "", type);
}
