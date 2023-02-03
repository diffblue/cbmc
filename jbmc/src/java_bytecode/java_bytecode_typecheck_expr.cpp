/*******************************************************************\

Module: JAVA Bytecode Conversion / Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Conversion / Type Checking

#include "java_bytecode_typecheck.h"

#include <util/pointer_expr.h>
#include <util/std_code.h>

#include "java_pointer_casts.h"
#include "java_string_literal_expr.h"

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
    !can_cast_expr<java_string_literal_exprt>(expr),
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
  const irep_idt &identifier = expr.get_identifier();

  // the java_bytecode_convert_class and java_bytecode_convert_method made sure
  // "identifier" exists in the symbol table
  const symbolt &symbol = symbol_table.lookup_ref(identifier);

  INVARIANT(!symbol.is_type, "symbol identifier should not be a type");

  // type the expression
  expr.type() = symbol.type;
}
