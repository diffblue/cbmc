/*******************************************************************\

Module:

Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

\*******************************************************************/

#include <assert.h>

#include <arith_tools.h>
#include <std_expr.h>
#include <solvers/flattening/boolbv_type.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/boolbv.h>

#include "z3_conv.h"

/*******************************************************************\

Function: z3_convt::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt z3_convt::get(const exprt &expr) const
{
  if(expr.id()=="symbol" ||
     expr.id()=="nondet_symbol")
  {
	std::string identifier, tmp;
	std::vector<exprt> unknown;
	Z3_ast bv;

	identifier = expr.get_string("identifier");

	map_varst::const_iterator cache_result=map_vars.find(identifier.c_str());
	if(cache_result!=map_vars.end())
	{
	  bv = cache_result->second;
	  return bv_get_rec(bv, unknown, true, expr.type());
	}

	return bv_get_rec(bv, unknown, false, expr.type());
  }
  else if(expr.id()=="constant")
    return expr;

  return expr;
}

/*******************************************************************\

Function: z3_convt::bv_get_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_convt::fill_vector(
  const Z3_ast &bv,
  std::vector<exprt> &unknown,
  const typet &type) const
{
  unsigned i, width;
  static unsigned int idx;
  Z3_app app = Z3_to_app(z3_ctx, bv);
  unsigned num_fields = Z3_get_app_num_args(z3_ctx, app);
  Z3_ast tmp;
  std::string value;

  for (i = 0; i < num_fields; i++)
  {
    tmp = Z3_get_app_arg(z3_ctx, app, i);

    if (Z3_get_ast_kind(z3_ctx, tmp)==Z3_NUMERAL_AST)
    {
      boolbv_get_width(type, width);
      value= Z3_get_numeral_string(z3_ctx, tmp);
      constant_exprt value_expr(type);
      value_expr.set_value(integer2binary(string2integer(value),width));

      if (i==1)
        idx = atoi(value.c_str());
      else if (i==2)
        if (idx<unknown.size())
          unknown[idx] = value_expr;
    }
    else
    {
      fill_vector(tmp, unknown, type);
    }
  }
}

/*******************************************************************\

Function: z3_convt::bv_get_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt z3_convt::bv_get_rec(
  const Z3_ast &bv,
  std::vector<exprt> &unknown,
  const bool cache,
  const typet &type) const
{
  unsigned width;

  if(boolbv_get_width(type, width))
    return nil_exprt();

  if(type.id()=="bool")
  {
	std::string value;
	size_t found;

	if (cache)
	{
	  Z3_app app = Z3_to_app(z3_ctx, bv);
	  Z3_func_decl d = Z3_get_app_decl(z3_ctx, app);
	  value = Z3_func_decl_to_string(z3_ctx, d);
      found=value.find("true");
	}
	else
	{
	  found=std::string::npos;
	}

    if (found!=std::string::npos)
  	  return true_exprt();
    else
      return false_exprt(); // default
  }

  bvtypet bvtype=get_bvtype(type);

  if(bvtype==IS_UNKNOWN)
  {
    if(type.id()=="array")
    {
      unsigned sub_width;
      const typet &subtype=type.subtype();

      if(!boolbv_get_width(subtype, sub_width))
      {
        exprt expr;
        static exprt::operandst op;
        constant_exprt zero_expr(subtype);

        op.reserve(width/sub_width);
        unsigned num_fields = Z3_get_app_num_args(z3_ctx, Z3_to_app(z3_ctx, bv));

        if (num_fields==0)
          return nil_exprt();

        unknown.resize(width/sub_width);

        fill_vector(bv, unknown, subtype);

        if (unknown.size()==0)
          return nil_exprt();

        unsigned int size=unknown.size();
        zero_expr.set_value("0");

        for(unsigned i=0; i<size; i++)
        {
          expr = unknown[i];

          if (expr.get_string("value").compare("")==0)
            op.push_back(zero_expr);
          else
            op.push_back(expr);
        }

        if (op.empty())
          return nil_exprt();

        exprt dest=exprt("array", type);
        dest.operands().swap(op);
        return dest;
      }
    }
    else if(type.id()=="struct")
    {
      const irept &components=type.find("components");
      exprt::operandst op;
      op.reserve(components.get_sub().size());
      unsigned int size;

      size = components.get_sub().size();

      exprt expr;
      unsigned i=0;
      Z3_app app = Z3_to_app(z3_ctx, bv);
      unsigned num_fields = Z3_get_app_num_args(z3_ctx, app);
      Z3_ast tmp;

      if (num_fields == 0)
    	return nil_exprt();

      forall_irep(it, components.get_sub())
      {
        const typet &subtype=static_cast<const typet &>(it->find("type"));
        op.push_back(nil_exprt());

        unsigned sub_width;
        if(!boolbv_get_width(subtype, sub_width))
        {
          tmp = Z3_get_app_arg(z3_ctx, app, i);
          expr=bv_get_rec(tmp, unknown, true, subtype);
          if (!expr.is_nil())
            unknown.push_back(expr);
          op.back()=unknown.back();
          ++i;
        }
      }

      exprt dest=exprt(type.id(), type);
      dest.operands().swap(op);

      return dest;
    }
    else if(type.id()=="union")
    {
      //@TODO: reconstruct the counter-example for unions
      return nil_exprt();

    }
  }

  std::string value;
  Z3_ast_kind ast_kind;

  ast_kind = Z3_get_ast_kind(z3_ctx, bv);

  if (ast_kind==Z3_NUMERAL_AST)
	value= Z3_get_numeral_string(z3_ctx, bv);
  else
    return nil_exprt();

  switch(bvtype)
  {
  case IS_C_ENUM:
    {
      constant_exprt value_expr(type);
      value_expr.set_value(value);
      return value_expr;
    }
    break;

  case IS_UNKNOWN:
    break;

  case IS_RANGE:
    {
      mp_integer int_value=string2integer(value, false);
      mp_integer from=string2integer(type.get_string("from"));

      constant_exprt value_expr(type);
      value_expr.set_value(integer2string(int_value+from));
      return value_expr;
    }
    break;

  default:
    unsigned width;
    boolbv_get_width(type, width);
    constant_exprt value_expr(type);
    value_expr.set_value(integer2binary(string2integer(value),width));
    return value_expr;
  }

  return nil_exprt();
}

