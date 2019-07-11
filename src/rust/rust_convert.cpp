/*******************************************************************\

Module: Rust Language Conversion

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language Conversion

#include "rust_convert.h"

#include <util/message.h>
#include <util/symbol_table.h>

#include "rust_parse_tree.h"

class rust_convertt : public messaget
{
public:
  rust_convertt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler)
    : messaget(_message_handler), symbol_table(_symbol_table)
  {
  }

  bool operator()(const rust_parse_treet &parse_tree);

protected:
  symbol_tablet &symbol_table;

  bool convert_code(const symbolt &symbol, codet &code);
};

bool rust_convertt::operator()(const rust_parse_treet &parse_tree)
{
  for(rust_parse_treet::itemst::const_iterator it = parse_tree.items.begin();
      it != parse_tree.items.end();
      ++it)
  {
    symbolt new_symbol;
    it->to_symbol(new_symbol);

    if(convert_code(new_symbol, to_code(new_symbol.value)))
      return true;

    if(const auto maybe_symbol = symbol_table.lookup(new_symbol.name))
    {
      const symbolt &s = *maybe_symbol;
      if(s.value.id() == "no-body-just-yet")
      {
        symbol_table.remove(s.name);
      }
    }
    if(symbol_table.add(new_symbol))
    {
      error() << "duplicate symbol " << new_symbol.name << eom;
      throw 0;
    }
  }

  return false;
}

bool rust_convertt::convert_code(const symbolt &symbol, codet &code)
{
  if(code.get_statement() == ID_block)
  {
    Forall_operands(it, code)
      if(convert_code(symbol, to_code(*it)))
        return true;
  }
  else if(code.get_statement() == ID_assign)
  {
    code_assignt &a = to_code_assign(code);

    if(a.rhs().id() == ID_with)
    {
      exprt to_try = a.rhs().op0();
      codet t(code_assignt(a.lhs(), to_try));
      if(convert_code(symbol, t))
        return true;

      irep_idt c_target = to_symbol_expr(a.rhs().op1()).get_identifier();
      code_gotot g(c_target);

      code_try_catcht t_c(std::move(t));
      // Adding empty symbol to catch decl
      code_declt d(symbol_exprt::typeless("decl_symbol"));
      t_c.add_catch(d, g);
      t_c.add_source_location() = code.source_location();

      code.swap(t_c);
    }
    else if(
      a.rhs().id() == ID_side_effect &&
      to_side_effect_expr(a.rhs()).get_statement() == ID_function_call)
    {
      side_effect_expr_function_callt f_expr =
        to_side_effect_expr_function_call(a.rhs());

      code_function_callt f(a.lhs(), f_expr.function(), f_expr.arguments());
      f.add_source_location() = code.source_location();

      code.swap(f);
    }
  }

  return false;
}

bool rust_convert(
  const rust_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  rust_convertt rust_convert(symbol_table, message_handler);

  try
  {
    return rust_convert(parse_tree);
  }

  catch(int)
  {
  }

  catch(const char *e)
  {
    rust_convert.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    rust_convert.error() << e << messaget::eom;
  }

  return true;
}
