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

#include "boolector_dec.h"

extern "C" {
#include "include/boolector.h"
}

/*******************************************************************\

Function: boolector_convt::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt boolector_dect::get(const exprt &expr) const
{
  if(expr.id()=="symbol" ||
     expr.id()=="nondet_symbol")
  {
	std::string tmp;
	std::vector<exprt> unknown;
	BtorExp *bv;

	bv_cachet::const_iterator cache_result=bv_cache.find(expr);
	if(cache_result!=bv_cache.end())
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

Function: boolector_convt::bv_get_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt boolector_dect::bv_get_rec(
  BtorExp *bv,
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
	  value = boolector_bv_assignment(boolector_ctx, bv);
      found=value.find("1");
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
#if 0
      unsigned sub_width;
      const typet &subtype=type.subtype();

      if(!boolbv_get_width(subtype, sub_width))
      {
    	  unsigned i, size=width/sub_width;
    	  std::cout << "size: " << size << "\n";
    	  int array_size;
    	  char **idx, **val;

    	  std::cout << "var: " << boolector_get_symbol_of_var(boolector_ctx, bv) << "\n";
    	  boolector_array_assignment(boolector_ctx, bv, &idx, &val, &array_size);
    	  std::cout << "is array: " << boolector_is_array(boolector_ctx, bv) << "\n";
    	  std::cout << "cache: " << cache << "\n";
    	  std::cout << "array_size: " << array_size << "\n";

    	  if (array_size > 0)
    	  {
    	    for (i = 0; i < array_size; i++)
    	    {
    	      std::cout << "idx: " << idx[i] << "val: " << val[i] << "\n";
    	      boolector_free_bv_assignment (boolector_ctx, idx[i]);
    	      boolector_free_bv_assignment (boolector_ctx, val[i]);
    	    }
    	    delete (idx);
    	    delete (val);
    	  }

      }
#endif
      return nil_exprt();
    }
    else if(type.id()=="struct")
    {
#if 0
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
#endif
      return nil_exprt();
    }
    else if(type.id()=="union")
    {
      //@TODO: reconstruct the counter-example for unions
      return nil_exprt();

    }
  }

  std::string value;

  if (cache)
    value = boolector_bv_assignment(boolector_ctx, bv);

  switch(bvtype)
  {
  case IS_C_ENUM:
    {
      constant_exprt value_expr(type);
      value_expr.set_value(integer2string(binary2integer(value, true)));
      return value_expr;
    }
    break;

  case IS_UNKNOWN:
    break;

  case IS_RANGE:
    {
      mp_integer int_value=binary2integer(value, false);
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
    value_expr.set_value(value);
    return value_expr;
  }

  return nil_exprt();
}
