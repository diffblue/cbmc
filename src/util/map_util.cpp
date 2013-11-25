/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "replace_expr.h"
#include "map_util.h"

/*******************************************************************\

Function: mapping_to_lambda

  Inputs:

 Outputs:

 Purpose: converts a mapping type to an incomplete lambda
          expression

\*******************************************************************/

void mapping_to_lambda(const typet &type, exprt &expr)
{
  if(type.id()!="mapping")
    throw "expected mapping type";

  if(type.subtypes().size()!=2)
    throw "mapping type expected to have two subtypes";

  const typet &domain=type.subtypes()[0];
  const typet &range =type.subtypes()[1];

  expr.clear();
  expr.id("lambda");
  expr.type()=type;
  expr.operands().resize(2);
  expr.op1().type()=range;

  exprt &op=expr.op0();
  op.type()=domain;

  if(domain.id()=="tuple")
  {
    op.id("tuple");

    op.operands().resize(domain.subtypes().size());

    typet::subtypest::const_iterator
      s_it=domain.subtypes().begin();
    
    Forall_operands(t_it, op)
    {
      *t_it=exprt("quant_symbol", *s_it);
      s_it++;
    }
  }
  else
    op.id("quant_symbol");
}

/*******************************************************************\

Function: tuple_component

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void tuple_component(const exprt &src, unsigned nr, exprt &dest)
{
  dest.clear();

  if(src.id()=="tuple")
  {
    if(nr>=src.operands().size())
      throw "tuple has not enough components";

    dest=src.operands()[nr];
  }
  else
  {
    dest.id(ID_member);
    dest.set(ID_component, nr);
    dest.copy_to_operands(src);
  }
}

/*******************************************************************\

Function: expand_map

  Inputs:

 Outputs:

 Purpose: expands a map operator

\*******************************************************************/

void expand_map(exprt &expr)
{
  // sanity checks

  if(expr.id()!="map")
    throw "expected mapping";

  if(expr.operands().size()!=2)
    throw "mapping takes two operands";

  exprt &lambda=expr.op0();

  if(lambda.id()!="lambda")
    throw "expected lambda expression as first operand";

  if(lambda.operands().size()!=2)
    throw "lambda takes two operands";

  // build replace_map

  replace_mapt replace_map;

  if(lambda.op0().id()=="tuple")
  {
    unsigned nr=0;

    forall_operands(it, lambda.op0())
    {
      exprt tmp;
      tuple_component(expr.op1(), nr, tmp);
      replace_map.insert(std::pair<exprt, exprt>(*it, tmp));
      nr++;
    }
  }
  else
    replace_map.insert
      (std::pair<exprt, exprt>(lambda.op0(), expr.op1()));

  // build new expression

  exprt new_expr;
  new_expr.swap(lambda.op1());
  replace_expr(replace_map, new_expr);
  expr.swap(new_expr);
}
