/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Conversion / Type Checking

#include "java_bytecode_typecheck.h"

#include <util/arith_tools.h>
#include <util/expr_initializer.h>
#include <util/unicode.h>

#include "java_pointer_casts.h"
#include "java_types.h"
#include "java_utils.h"
#include "java_root_class.h"
#include "java_string_library_preprocess.h"

void java_bytecode_typecheckt::typecheck_expr(exprt &expr)
{
  if(expr.id()==ID_code)
    return typecheck_code(to_code(expr));

  if(expr.id()==ID_typecast &&
     expr.type().id()==ID_pointer)
    expr=make_clean_pointer_cast(
      expr,
      to_pointer_type(expr.type()),
      ns);

  // do operands recursively
  Forall_operands(it, expr)
    typecheck_expr(*it);

  INVARIANT(
    expr.id() != ID_java_string_literal,
    "String literals should have been converted to constant globals "
    "before typecheck_expr");

  if(expr.id()==ID_symbol)
    typecheck_expr_symbol(to_symbol_expr(expr));
  else if(expr.id()==ID_side_effect)
  {
    const irep_idt &statement=to_side_effect_expr(expr).get_statement();
    if(statement==ID_java_new)
      typecheck_expr_java_new(to_side_effect_expr(expr));
    else if(statement==ID_java_new_array)
      typecheck_expr_java_new_array(to_side_effect_expr(expr));
  }
}

void java_bytecode_typecheckt::typecheck_expr_java_new(side_effect_exprt &expr)
{
  PRECONDITION(expr.operands().empty());
  typet &type=expr.type();
  typecheck_type(type);
}

void java_bytecode_typecheckt::typecheck_expr_java_new_array(
  side_effect_exprt &expr)
{
  PRECONDITION(expr.operands().size()>=1); // one per dimension
  typet &type=expr.type();
  typecheck_type(type);
}

void java_bytecode_typecheckt::typecheck_expr_symbol(symbol_exprt &expr)
{
  irep_idt identifier=expr.get_identifier();

  // does it exist already in the destination symbol table?
  symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(identifier);

  if(s_it==symbol_table.symbols.end())
  {
    PRECONDITION(
      has_prefix(id2string(identifier), "java::") ||
      has_prefix(id2string(identifier), CPROVER_PREFIX));

    // no, create the symbol
    symbolt new_symbol;
    new_symbol.name=identifier;
    new_symbol.type=expr.type();
    new_symbol.base_name=expr.get(ID_C_base_name);
    new_symbol.pretty_name=id2string(identifier).substr(6, std::string::npos);
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;

    if(new_symbol.type.id()==ID_code)
    {
      new_symbol.is_lvalue=false;
    }
    else
    {
      new_symbol.is_lvalue=true;
    }

    if(symbol_table.add(new_symbol))
    {
      error() << "failed to add expression symbol to symbol table" << eom;
      throw 0;
    }
  }
  else
  {
    // yes!
    INVARIANT(!s_it->second.is_type, "symbol identifier should not be a type");

    const symbolt &symbol=s_it->second;

    // type the expression
    expr.type()=symbol.type;
  }
}
