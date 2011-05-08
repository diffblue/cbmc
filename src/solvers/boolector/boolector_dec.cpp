/*******************************************************************\

Module:

Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

\*******************************************************************/

#include <assert.h>
#include <ctype.h>
#include <math.h>

#include <sstream>

#include <unistd.h>
#include <str_getline.h>
#include <arith_tools.h>
#include <std_types.h>
#include <config.h>
#include <i2string.h>
#include <expr_util.h>
#include <prefix.h>
#include <string2array.h>
#include <pointer_offset_size.h>
#include <find_symbols.h>

#include <ansi-c/c_types.h>
#include <solvers/flattening/boolbv_width.h>

#include "boolector_dec.h"

extern "C" {
#include "include/boolector.h"
}

#define DEBUG

/*******************************************************************\

Function: boolector_dect::boolector_dect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

boolector_dect::boolector_dect():prop_convt(boolector_prop)
{
  number_variables_boolector=0;
  set_to_counter=0;
  boolector_prop.boolector_ctx = boolector_new();
  boolector_ctx = boolector_prop.boolector_ctx;
  boolector_enable_model_gen(boolector_ctx);

  //boolector_enable_inc_usage(boolector_ctx);
  //btorFile = fopen ( "btor.txt" , "wb" );
  //smtFile = fopen ( "smt.txt" , "wb" );
}

/*******************************************************************\

Function: boolector_dect::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt boolector_dect::dec_solve()
{
  //status("Number of variables: " + integer2string(get_number_variables_boolector()));

  post_process();
  status("Solving with SMT solver Boolector");

  return read_boolector_result();
}

/*******************************************************************\

Function: boolector_dect::read_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolector_dect::read_assert(std::istream &in, std::string &line)
{
}

/*******************************************************************\

Function: boolector_dect::read_boolector_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt boolector_dect::read_boolector_result()
{
  int result;

  result = check_boolector_properties();


  if (result==BOOLECTOR_UNSAT)
	return D_UNSATISFIABLE;
  else if (result==BOOLECTOR_SAT)
	return D_SATISFIABLE;

  error("Unexpected result from Boolector");

  return D_ERROR;
}

/*******************************************************************
 Function: boolector_dect::print_data_types

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void boolector_dect::print_data_types(BtorExp* operand0, BtorExp* operand1)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::check_all_types

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool boolector_dect::check_all_types(const typet &type)
{
  if (type.id()=="bool" || type.id()=="signedbv" || type.id()=="unsignedbv" ||
	  type.id()=="symbol" || type.id()=="empty" || type.id() == "fixedbv" ||
	  type.id()=="array" || type.id()=="struct" || type.id()=="pointer" ||
	  type.id()=="union")
  {
    return true;
  }

  return false;
}

/*******************************************************************
 Function: boolector_dect::is_signed

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool boolector_dect::is_signed(const typet &type)
{
  if (type.id()=="signedbv" || type.id()=="fixedbv")
    return true;

  return false;
}

/*******************************************************************
 Function: boolector_dect::check_boolector_properties

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

int boolector_dect::check_boolector_properties(void)
{
  return boolector_sat(boolector_ctx);
}

/*******************************************************************
 Function: boolector_dect::is_ptr

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool boolector_dect::is_ptr(const typet &type)
{
  return type.id()=="pointer" || type.id()=="reference";
}

/*******************************************************************
 Function: boolector_dect::convert_pointer_offset

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_pointer_offset(unsigned bits)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}
/*******************************************************************
 Function: boolector_dect::select_pointer_value

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::select_pointer_value(BtorExp* object, BtorExp* offset)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::create_boolector_array

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::create_boolector_array(const typet &type, std::string identifier)
{
  BtorExp *array;
  unsigned int width = 0;

  if (type.subtype().id() == "bool")
  {
    array = boolector_array(boolector_ctx, 1, config.ansi_c.int_width, identifier.c_str());
  }
  else if (type.subtype().id() == "fixedbv")
  {
	width = atoi(type.subtype().get("width").c_str());
	array = boolector_array(boolector_ctx, width, config.ansi_c.int_width, identifier.c_str());
  }
  else if (type.subtype().id() == "signedbv" || type.subtype().id() == "unsignedbv")
  {
	width = atoi(type.subtype().get("width").c_str());
	array = boolector_array(boolector_ctx, width, config.ansi_c.int_width, identifier.c_str());
  }
  else if (type.subtype().id() == "pointer")
  {
	array = create_boolector_array(type.subtype(), identifier);
  }

  return array;
}

/*******************************************************************
 Function: boolector_dect::convert_identifier

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_identifier(const std::string &identifier, const typet &type)
{
  BtorExp* identifier_var;
  unsigned int width = 0;

  width = atoi(type.get("width").c_str());

  if (type.id()=="bool")
  {
	identifier_var = boolector_var(boolector_ctx, 1, identifier.c_str());
  }
  else if (type.id()=="signedbv" || type.id()=="unsignedbv")
  {
    identifier_var = boolector_var(boolector_ctx, width, identifier.c_str());
  }
  else if (type.id()== "fixedbv")
  {
	identifier_var = boolector_var(boolector_ctx, width, identifier.c_str());
  }
  else if (type.id()=="array")
  {
	identifier_var = create_boolector_array(type, identifier);
  }
  else if (type.id()=="pointer")
  {
	identifier_var = convert_identifier(identifier, type.subtype());
  }

  ++number_variables_boolector;

  return identifier_var;
}

/*******************************************************************\

Function: boolector_dect::convert_bv
  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

BtorExp* boolector_dect::convert_bv(const exprt &expr)
{
  bv_cachet::const_iterator cache_result=bv_cache.find(expr);
  if(cache_result!=bv_cache.end())
  {
    //std::cout << "Cache hit on " << expr.pretty() << "\n";
    return cache_result->second;
  }

  BtorExp* result;

  result = convert_boolector_expr(expr);

  // insert into cache
  bv_cache.insert(std::pair<const exprt, BtorExp*>(expr, result));

  return result;
}

/*******************************************************************
 Function: boolector_dect::read_cache

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::read_cache(const exprt &expr)
{
  std::string symbol;
  unsigned int size = pointer_cache.size();

  symbol = expr.get_string("identifier");

  for(pointer_cachet::const_iterator it = pointer_cache.begin();
  it != pointer_cache.end(); it++)
  {
	if (symbol.compare((*it).second.c_str())==0)
	{
	  //std::cout << "Cache hit on: " << (*it).first.pretty() << "\n";
	  return convert_bv((*it).first);
	}
  }

  return convert_bv(expr);
}

/*******************************************************************
 Function: boolector_dect::write_cache

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void boolector_dect::write_cache(const exprt &expr)
{
  std::string symbol, identifier;

  identifier = expr.get_string("identifier");

  for (std::string::const_iterator it = identifier.begin(); it
		!= identifier.end(); it++)
  {
	char ch = *it;

	if (isalnum(ch) || ch == '$' || ch == '?')
	{
	  symbol += ch;
	}
	else if (ch == '#')
	{
      pointer_cache.insert(std::pair<const exprt, std::string>(expr, symbol));
      return;
	}
  }
}

/*******************************************************************
 Function: boolector_dect::convert_lt

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_lt(const exprt &expr)
{
  assert(expr.operands().size()==2);
  BtorExp *constraint, *operand0, *operand1;

  if (expr.op0().type().id()=="array")
    write_cache(expr.op0());

  operand0 = convert_bv(expr.op0());
  operand1 = convert_bv(expr.op1());

  if (expr.op1().type().id()=="signedbv" || expr.op1().type().id()=="fixedbv")
	constraint = boolector_slt(boolector_ctx, operand0, operand1);
  else if (expr.op1().type().id()=="unsignedbv")
	constraint = boolector_ult(boolector_ctx, operand0, operand1);

  return constraint;
}

/*******************************************************************
 Function: boolector_dect::convert_gt

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_gt(const exprt &expr)
{
  assert(expr.operands().size()==2);
  BtorExp *constraint, *operand0, *operand1;

  if (expr.op0().type().id()=="array")
    write_cache(expr.op0());

  operand0 = convert_bv(expr.op0());
  operand1 = convert_bv(expr.op1());

  if (expr.op1().type().id()=="signedbv" || expr.op1().type().id()=="fixedbv")
	constraint = boolector_sgt(boolector_ctx, operand0, operand1);
  else if (expr.op1().type().id()=="unsignedbv")
	constraint = boolector_ugt(boolector_ctx, operand0, operand1);

  return constraint;
}


/*******************************************************************
 Function: boolector_dect::convert_le

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_le(const exprt &expr)
{
  assert(expr.operands().size()==2);
  BtorExp *constraint, *operand0, *operand1;

  if (expr.op0().type().id()=="array")
    write_cache(expr.op0());

  operand0 = convert_bv(expr.op0());
  operand1 = convert_bv(expr.op1());

  if (expr.op1().type().id()=="signedbv" || expr.op1().type().id()=="fixedbv")
	constraint = boolector_slte(boolector_ctx, operand0, operand1);
  else if (expr.op1().type().id()=="unsignedbv")
	constraint = boolector_ulte(boolector_ctx, operand0, operand1);

  return constraint;
}

/*******************************************************************
 Function: boolector_dect::convert_ge

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_ge(const exprt &expr)
{
  assert(expr.operands().size()==2);
  BtorExp *constraint, *operand0, *operand1;

  if (expr.op0().type().id()=="array")
    write_cache(expr.op0());

  operand0 = convert_bv(expr.op0());
  operand1 = convert_bv(expr.op1());

  if (expr.op1().type().id()=="signedbv" || expr.op1().type().id()=="fixedbv")
	constraint = boolector_sgte(boolector_ctx, operand0, operand1);
  else if (expr.op1().type().id()=="unsignedbv")
	constraint = boolector_ugte(boolector_ctx, operand0, operand1);

  return constraint;
}


/*******************************************************************
 Function: boolector_dect::convert_eq

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_eq(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static BtorExp *constraint, *operand0, *operand1;

  if (expr.op0().type().id()=="array")
    write_cache(expr.op0());

  operand0 = convert_bv(expr.op0());
  operand1 = convert_bv(expr.op1());

  if (expr.id() == "=")
	constraint = boolector_eq(boolector_ctx, operand0, operand1);
  else
	constraint = boolector_ne(boolector_ctx, operand0, operand1);

  return constraint;
}

/*******************************************************************
 Function: boolector_dect::convert_invalid_pointer

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_invalid(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::convert_same_object

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_same_object(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::convert_dynamic_object

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_dynamic_object(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::convert_overflow_sum

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_overflow_sum(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static BtorExp *bv, *operand[2];

  operand[0] = convert_bv(expr.op0());
  operand[1] = convert_bv(expr.op1());

  if (expr.op0().type().id()=="signedbv" && expr.op1().type().id()=="signedbv")
    bv = boolector_saddo(boolector_ctx, operand[0], operand[1]);
  else if (expr.op0().type().id()=="unsignedbv" && expr.op1().type().id()=="unsignedbv")
	bv = boolector_uaddo(boolector_ctx, operand[0], operand[1]);

  return bv; //boolector_not(boolector_ctx, bv);
}

/*******************************************************************
 Function: boolector_dect::convert_overflow_sub

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_overflow_sub(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static BtorExp *bv, *operand[2];

  operand[0] = convert_bv(expr.op0());
  operand[1] = convert_bv(expr.op1());

  if (expr.op0().type().id()=="signedbv" && expr.op1().type().id()=="signedbv")
    bv = boolector_ssubo(boolector_ctx, operand[0], operand[1]);
  else if (expr.op0().type().id()=="unsignedbv" && expr.op1().type().id()=="unsignedbv")
	bv = boolector_usubo(boolector_ctx, operand[0], operand[1]);

  return bv; //boolector_not(boolector_ctx, bv);
}

/*******************************************************************
 Function: boolector_dect::convert_overflow_mul

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_overflow_mul(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static BtorExp *bv, *operand[2];

  operand[0] = convert_bv(expr.op0());
  operand[1] = convert_bv(expr.op1());

  if (expr.op0().type().id()=="signedbv" && expr.op1().type().id()=="signedbv")
    bv = boolector_smulo(boolector_ctx, operand[0], operand[1]);
  else if (expr.op0().type().id()=="unsignedbv" && expr.op1().type().id()=="unsignedbv")
	bv = boolector_umulo(boolector_ctx, operand[0], operand[1]);

  return bv; //boolector_not(boolector_ctx, bv);
}

/*******************************************************************
 Function: boolector_dect::convert_overflow_unary

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_overflow_unary(const exprt &expr)
{
  assert(expr.operands().size()==1);
  static BtorExp *bv, *operand;
  u_int i, width;

  operand = convert_bv(expr.op0());
  boolbv_get_width(expr.op0().type(), width);

  if (expr.op0().type().id()=="signedbv")
    bv = boolector_slt(boolector_ctx, boolector_neg(boolector_ctx, operand), boolector_ones(boolector_ctx,width));
  else if (expr.op0().type().id()=="unsignedbv")
	bv = boolector_slt(boolector_ctx, boolector_neg(boolector_ctx, operand), boolector_ones(boolector_ctx,width));

  return bv;
}

/*******************************************************************
 Function: boolector_dect::convert_overflow_typecast

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_overflow_typecast(const exprt &expr)
{
  unsigned bits=atoi(expr.id().c_str()+18);

  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=1)
    throw "operand "+expr.id_string()+" takes one operand";

  static BtorExp *bv, *operand[3], *mid, *overflow[2], *tmp, *minus_one, *two;
  u_int i, result=1, width;
  std::string value;

  boolbv_get_width(expr.op0().type(), width);

  if(bits>=width || bits==0)
    throw "overflow-typecast got wrong number of bits";

  assert(bits <= 32);

  for(i=0; i<bits; i++)
  {
	if (i==31)
	  result=(result-1)*2+1;
	else if (i<31)
      result*=2;
  }

  if (is_signed(expr.op0().type()))
    value = integer2string(binary2integer(expr.op0().get_string("value"), true),10);
  else
	value = integer2string(binary2integer(expr.op0().get_string("value"), false),10);

  operand[0] = convert_bv(expr.op0());

  if (expr.op0().type().id()=="signedbv" || expr.op0().type().id()=="fixedbv")
  {
	tmp = boolector_int(boolector_ctx, result, width);
	two = boolector_int(boolector_ctx, 2, width);
	minus_one = boolector_int(boolector_ctx, -1, width);
	mid = boolector_sdiv(boolector_ctx, tmp, two);
	operand[1] = boolector_sub(boolector_ctx, mid, minus_one);
	operand[2] = boolector_mul(boolector_ctx, operand[1], minus_one);

	overflow[0] = boolector_slt(boolector_ctx, operand[0], operand[1]);
	overflow[1] = boolector_sgt(boolector_ctx, operand[0], operand[2]);
	bv = boolector_not(boolector_ctx, boolector_and(boolector_ctx, overflow[0], overflow[1]));
  }
  else if (expr.op0().type().id()=="unsignedbv")
  {
	operand[2] = boolector_unsigned_int(boolector_ctx, 0, width);
	operand[1] = boolector_unsigned_int(boolector_ctx, result, width);
	overflow[0] = boolector_ult(boolector_ctx, operand[0], operand[1]);
	overflow[1] = boolector_ugt(boolector_ctx, operand[0], operand[2]);
	bv = boolector_not(boolector_ctx, boolector_and(boolector_ctx, overflow[0], overflow[1]));
  }

  return bv;
}

/*******************************************************************
 Function: boolector_dect::convert_rest

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

literalt boolector_dect::convert_rest(const exprt &expr)
{
  assert(expr.type().id()=="bool");

  if(expr.is_true())
    return const_literal(true);
  else if(expr.is_false())
    return const_literal(false);

  literalt l = boolector_prop.new_variable();
  static BtorExp *constraint, *formula;

  //std::cout << "convert_rest: " << l.var_no() << "\n";

  if (!assign_boolector_expr(expr))
	return l;

  if (expr.id() == "=" || expr.id() == "notequal")
	constraint = convert_eq(expr);
  else if (expr.id() == "<")
	constraint = convert_lt(expr);
  else if (expr.id() == ">")
	constraint = convert_gt(expr);
  else if (expr.id() == "<=")
	constraint = convert_le(expr);
  else if (expr.id() == ">=")
	constraint = convert_ge(expr);
  else if (expr.id() == "overflow-+")
	constraint = convert_overflow_sum(expr);
  else if (expr.id() == "overflow--")
	constraint = convert_overflow_sub(expr);
  else if (expr.id() == "overflow-*")
	constraint = convert_overflow_mul(expr);
  else if (expr.id() == "overflow-unary-")
	constraint = convert_overflow_unary(expr);
  else if(has_prefix(expr.id_string(), "overflow-typecast-"))
	constraint = convert_overflow_typecast(expr);
  else
	throw "convert_boolector_expr: " + expr.id_string() + " is not supported yet";

  formula = boolector_iff(boolector_ctx, boolector_prop.boolector_literal(l), constraint);
  boolector_assert(boolector_ctx, formula);

  //boolector_dump_btor(boolector_ctx, btorFile, formula);
  //boolector_dump_smt(boolector_ctx, smtFile, formula);

  return l;
}

/*******************************************************************
 Function: boolector_dect::convert_rel

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_rel(const exprt &expr)
{
  assert(expr.operands().size()==2);

  BtorExp *result, *operand0, *operand1;

  operand0 = convert_bv(expr.op0());
  operand1 = convert_bv(expr.op1());

  const typet &op_type=expr.op0().type();

  if (op_type.id()=="unsignedbv" || op_type.subtype().id()=="unsignedbv")
  {
    if(expr.id()=="<=")
   	  result = boolector_ulte(boolector_ctx,operand0,operand1);
    else if(expr.id()=="<")
      result = boolector_ult(boolector_ctx,operand0,operand1);
    else if(expr.id()==">=")
      result = boolector_ugt(boolector_ctx,operand0,operand1);
    else if(expr.id()==">")
      result = boolector_ugte(boolector_ctx,operand0,operand1);
  }
  else if (op_type.id()=="signedbv" || op_type.id()=="fixedbv" ||
			 op_type.subtype().id()=="signedbv" || op_type.subtype().id()=="fixedbv" )
  {
    if(expr.id()=="<=")
      result = boolector_slte(boolector_ctx,operand0,operand1);
    else if(expr.id()=="<")
      result = boolector_ult(boolector_ctx,operand0,operand1);
    else if(expr.id()==">=")
      result = boolector_sgt(boolector_ctx,operand0,operand1);
    else if(expr.id()==">")
      result = boolector_sgte(boolector_ctx,operand0,operand1);
  }

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_typecast

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_typecast(const exprt &expr)
{
  assert(expr.operands().size()==1);

  BtorExp *result, *operand;
  const exprt &op=expr.op0();

  if(expr.type().id()=="signedbv" || expr.type().id()=="unsignedbv"
	  || expr.type().id()=="fixedbv")
  {
    unsigned to_width=atoi(expr.type().get("width").c_str());

    if(op.type().id()=="signedbv" || op.type().id()=="fixedbv")
    {
      unsigned from_width=atoi(op.type().get("width").c_str());
      //std::cout << "from_width: " << from_width << "\n";
      //std::cout << "to_width: " << to_width << "\n";

      if(from_width==to_width)
    	result = convert_bv(op);
      else if(from_width<to_width)
      {
    	  operand = convert_bv(op);
    	  result = boolector_sext(boolector_ctx, operand, (to_width-from_width));
      }
      else if (from_width>to_width)
      {
    	operand = convert_bv(op);
    	result = boolector_slice(boolector_ctx, operand, (to_width-1), 0);
      }
    }
    else if(op.type().id()=="unsignedbv")
    {
      unsigned from_width=atoi(op.type().get("width").c_str());
      //std::cout << "from_width: " << from_width << "\n";
      //std::cout << "to_width: " << to_width << "\n";

      if(from_width==to_width)
      {
    	result = convert_bv(op);
      }
      else if(from_width<to_width)
      {
    	//std::cout << "to_width-from_width: " << to_width-from_width << "\n";
    	operand = convert_bv(op);
    	result = boolector_uext(boolector_ctx, operand, (to_width-from_width));
      }
      else if (from_width>to_width)
      {
        //std::cout << "slice from_width: " << from_width << "\n";
        //std::cout << "slice to_width: " << to_width << "\n";
      	operand = convert_bv(op);
      	result = boolector_slice(boolector_ctx, operand, (to_width-1), 0);
      }
    }
    else if (op.type().id()=="bool")
    {
  	  BtorExp *zero, *one;
      unsigned width;

      boolbv_get_width(expr.type(), width);
  	  if (expr.type().id()=="signedbv" || expr.type().id()=="fixedbv")
  	  {
  	    zero = boolector_int(boolector_ctx, 0, width);
  	    one =  boolector_int(boolector_ctx, 1, width);
  	  }
  	  else if (expr.type().id()=="unsignedbv")
  	  {
  	    zero = boolector_unsigned_int(boolector_ctx, 0, width);
  	    one =  boolector_unsigned_int(boolector_ctx, 1, width);
  	  }

  	  operand = convert_bv(op);
  	  result = boolector_cond(boolector_ctx, operand, one, zero);
    }
  }

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_struct

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_struct(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::convert_union

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_union(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::convert_boolector_pointer

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_boolector_pointer(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::convert_zero_string

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_zero_string(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

  BtorExp *zero_string;

  zero_string =  create_boolector_array(expr.type(), "zero_string");

  return zero_string;
}

/*******************************************************************
 Function: boolector_dect::convert_array

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_array(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif
}

/*******************************************************************
 Function: boolector_dect::convert_constant_array

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_constant_array(const exprt &expr)
{
  unsigned int width=0, i=0;
  BtorExp *array_cte, *int_cte, *val_cte;
  std::string value_cte, tmp, identifier;
  char i_str[2];

  width = atoi(expr.type().subtype().get("width").c_str());
  identifier = expr.get_string("identifier") + expr.type().subtype().get("width").c_str();

  array_cte = create_boolector_array(expr.type(), identifier);

  i=0;
  forall_operands(it, expr)
  {
	sprintf(i_str,"%i",i);
    int_cte = boolector_int(boolector_ctx, atoi(i_str), config.ansi_c.int_width);
	if (is_signed(it->type()))
	  value_cte = integer2string(binary2integer(it->get("value").c_str(), true),10);
	else
	  value_cte = integer2string(binary2integer(it->get("value").c_str(), false),10);

	val_cte = boolector_int(boolector_ctx, atoi(value_cte.c_str()), width);
	array_cte = boolector_write(boolector_ctx, array_cte, int_cte, val_cte);
	++i;
  }

  return array_cte;
}

/*******************************************************************
 Function: boolector_dect::convert_constant

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_constant(const exprt &expr)
{
  BtorExp *const_var;
  std::string value;
  unsigned int width;

  if (is_signed(expr.type()))
    value = integer2string(binary2integer(expr.get_string("value"), true),10);
  else
	value = integer2string(binary2integer(expr.get_string("value"), false),10);

  width = atoi(expr.type().get("width").c_str());

  if (expr.type().id()=="bool")
  {
	if (expr.is_false())
	  const_var = boolector_false(boolector_ctx);
	else if (expr.is_true())
	  const_var = boolector_true(boolector_ctx);
  }
  else if (expr.type().id() == "signedbv" || expr.type().id() == "c_enum")
  {
	const_var = boolector_int(boolector_ctx, atoi(value.c_str()), width);
  }
  else if (expr.type().id() == "unsignedbv")
  {
	const_var = boolector_unsigned_int(boolector_ctx, atoi(value.c_str()), width);
  }
  else if (expr.type().id()== "fixedbv")
  {
	const_var = boolector_int(boolector_ctx, atoi(value.c_str()), width);
  }
  else if (expr.type().id()== "array")
  {
	const_var = convert_constant_array(expr);
  }
  else if (expr.type().id()== "pointer")
  {
	width = atoi(expr.type().subtype().get("width").c_str());
	const_var = boolector_int(boolector_ctx, atoi(value.c_str()), width);
  }

  return const_var;
}

/*******************************************************************
 Function: boolector_dect::convert_concatenation

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_concatenation(const exprt &expr) {

#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::convert_bitwise

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_bitwise(const exprt &expr)
{
  assert(expr.operands().size()==2);

  BtorExp *bitwise_var, *args[2];

  args[0] = convert_bv(expr.op0());
  args[1] = convert_bv(expr.op1());

  if(expr.id()=="bitand")
    bitwise_var = boolector_and(boolector_ctx, args[0], args[1]);
  else if(expr.id()=="bitor")
	bitwise_var = boolector_or(boolector_ctx, args[0], args[1]);
  else if(expr.id()=="bitxor")
	bitwise_var = boolector_xor(boolector_ctx, args[0], args[1]);
  else if (expr.id()=="bitnand")
	bitwise_var = boolector_nand(boolector_ctx, args[0], args[1]);
  else if (expr.id()=="bitnor")
	bitwise_var = boolector_nor(boolector_ctx, args[0], args[1]);
  else if (expr.id()=="bitnxor")
    bitwise_var = boolector_xnor(boolector_ctx, args[0], args[1]);

  return bitwise_var;
}

/*******************************************************************
 Function: boolector_dect::convert_unary_minus

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_unary_minus(const exprt &expr)
{
  assert(expr.operands().size()==1);

  BtorExp *result;

  result = boolector_neg(boolector_ctx, convert_bv(expr.op0()));

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_if

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_if(const exprt &expr)
{
  assert(expr.operands().size()==3);

  BtorExp *result, *operand0, *operand1, *operand2;

  operand0 = convert_bv(expr.op0());
  operand1 = convert_bv(expr.op1());
  operand2 = convert_bv(expr.op2());

  result = boolector_cond(boolector_ctx, operand0, operand1, operand2);

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_logical_ops

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_logical_ops(const exprt &expr)
{
  assert(expr.type().id()=="bool");
  assert(expr.operands().size()>=1);

  u_int i=0, size;

  size=expr.operands().size();
  BtorExp *args[size], *result;

  if (size==1)
  {
    result = convert_bv(expr.op0());
  }
  else
  {
	forall_operands(it, expr)
	{
	  args[i] = convert_bv(*it);

	  if (i>=1)
	  {
		if(expr.id()=="and")
		  args[i] = boolector_and(boolector_ctx, args[i-1], args[i]);
		else if(expr.id()=="or")
		  args[i] = boolector_or(boolector_ctx, args[i-1], args[i]);
		else if(expr.id()=="xor")
		  args[i] = boolector_xor(boolector_ctx, args[i-1], args[i]);
	  }

	  ++i;
	}

	result = args[size-1];
  }

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_logical_not

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_logical_not(const exprt &expr)
{
  assert(expr.operands().size()==1);

  BtorExp *operand0;

  operand0 = convert_bv(expr.op0());

  return boolector_not(boolector_ctx, operand0);
}

/*******************************************************************
 Function: boolector_dect::convert_equality

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_equality(const exprt &expr)
{
  assert(expr.operands().size()==2);
  assert(expr.op0().type()==expr.op1().type());

  BtorExp *result=0, *args[2];

  args[0] = convert_bv(expr.op0());
  args[1] = convert_bv(expr.op1());

  if (expr.id()=="=")
    result = boolector_eq(boolector_ctx, args[0], args[1]);
  else
	result = boolector_ne(boolector_ctx, args[0], args[1]);

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_add

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_add(const exprt &expr)
{
  assert(expr.operands().size()>=2);
  u_int i=0, size;

  size=expr.operands().size()+1;
  BtorExp *args[size];

  forall_operands(it, expr)
  {
	args[i] = convert_bv(*it);

    if (i==1)
      args[size-1] = boolector_add(boolector_ctx, args[0], args[1]);
    else if (i>1)
 	  args[size-1] = boolector_add(boolector_ctx, args[size-1], args[i]);
    ++i;
  }

  return args[i];
}

/*******************************************************************
 Function: boolector_dect::convert_sub

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_sub(const exprt &expr)
{
  assert(expr.operands().size()>=2);
  u_int i=0, size;

  size=expr.operands().size()+1;
  BtorExp *args[size];

  forall_operands(it, expr)
  {
	args[i] = convert_bv(*it);

    if (i==1)
      args[size-1] = boolector_sub(boolector_ctx, args[0], args[1]);
    else if (i>1)
 	  args[size-1] = boolector_sub(boolector_ctx, args[size-1], args[i]);
    ++i;
  }

  return args[i];
}

/*******************************************************************
 Function: boolector_dect::convert_div

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_div(const exprt &expr)
{
  assert(expr.operands().size()==2);

  BtorExp *result, *args[2], *overflow, *zero;

  args[0] = convert_bv(expr.op0());
  args[1] = convert_bv(expr.op1());

  if (expr.type().id()=="signedbv" || expr.type().id()=="fixedbv")
	result = boolector_sdiv(boolector_ctx, args[0], args[1]);
  else if (expr.type().id()=="unsignedbv")
	result = boolector_udiv(boolector_ctx, args[0], args[1]);

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_mod

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_mod(const exprt &expr)
{
  assert(expr.operands().size()==2);

  BtorExp *result, *operand0, *operand1;

  operand0 = convert_bv(expr.op0());
  operand1 = convert_bv(expr.op1());

  if(expr.type().id()=="signedbv")
	result = boolector_srem(boolector_ctx, operand0, operand1);
  else if (expr.type().id()=="unsignedbv")
	result = boolector_urem(boolector_ctx, operand0, operand1);
  else if (expr.type().id()=="fixedbv")
	throw "unsupported type for mod: "+expr.type().id_string();

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_mul

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_mul(const exprt &expr)
{
  assert(expr.operands().size()>=2);
  u_int i=0, size;

  size=expr.operands().size()+1;
  BtorExp *args[size];

  forall_operands(it, expr)
  {
	args[i] = convert_bv(*it);

    if (i==1)
      args[size-1] = boolector_mul(boolector_ctx, args[0], args[1]);
    else if (i>1)
 	  args[size-1] = boolector_mul(boolector_ctx, args[size-1], args[i]);
    ++i;
  }

  return args[i];
}

/*******************************************************************
 Function: boolector_dect::convert_pointer

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_pointer(const exprt &expr)
{
  assert(expr.operands().size()==1);
  assert(expr.type().id()=="pointer");

  BtorExp *result, *args[2];
  std::string symbol_name;

  if (expr.op0().id() == "index")
  {
    const exprt &object=expr.op0().operands()[0];
	const exprt &index=expr.op0().operands()[1];

    args[0] = read_cache(object);
	args[1] = convert_bv(index);

	result = boolector_read(boolector_ctx, args[0], args[1]);
  }

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_array_of

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_array_of(const exprt &expr)
{
  BtorExp *index, *value, *array_of_var;
  const array_typet &array_type_size=to_array_type(expr.type());
  std::string tmp;
  unsigned int j, size, width;

  tmp = integer2string(binary2integer(array_type_size.size().get_string("value"), false),10);
  size = atoi(tmp.c_str());
  width = atoi(expr.type().subtype().get("width").c_str());

  if (expr.type().subtype().id()=="bool")
  {
    value = boolector_false(boolector_ctx);
    array_of_var = boolector_array(boolector_ctx, 1, config.ansi_c.int_width,"ARRAY_OF(false)");
  }
  else if (expr.type().subtype().id()=="signedbv" || expr.type().subtype().id()=="unsignedbv")
  {
	value = convert_bv(expr.op0());
    array_of_var = boolector_array(boolector_ctx, width, config.ansi_c.int_width,"ARRAY_OF(0)");
  }
  else if (expr.type().subtype().id()=="fixedbv")
  {
	value = convert_bv(expr.op0());
    array_of_var = boolector_array(boolector_ctx, width, config.ansi_c.int_width, "ARRAY_OF(0l)");
  }
  else if (expr.type().subtype().id()=="pointer")
  {
	const exprt &object=expr.op0().operands()[0];
	const exprt &index=expr.op0().operands()[1];

	width = atoi(expr.op0().type().subtype().get("width").c_str());
	value = convert_bv(expr.op0());
	array_of_var = boolector_array(boolector_ctx, width, config.ansi_c.int_width, "&(ZERO_STRING())[0]");
  }

  if (size==0)
	size=1; //update at leat the first element of the array of bool

  //update array
  for (j=0; j<size; j++)
  {
    index = boolector_int(boolector_ctx, j, config.ansi_c.int_width);
    array_of_var = boolector_write(boolector_ctx, array_of_var, index, value);
  }

  return array_of_var;
}

/*******************************************************************
 Function: boolector_dect::convert_array_of_array

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_array_of_array(const std::string identifier, const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}


/*******************************************************************
 Function: boolector_dect::convert_index

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_index(const exprt &expr)
{
  assert(expr.operands().size()==2);

  BtorExp *array, *index;

  array = convert_bv(expr.op0());
  index = convert_bv(expr.op1());

  return boolector_read(boolector_ctx, array, index);
}

/*******************************************************************
 Function: boolector_dect::convert_constant

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_shift_constant(const exprt &expr)
{
  BtorExp *result;
  std::string value;
  unsigned int size, width;

  if (is_signed(expr.type()))
    value = integer2string(binary2integer(expr.get_string("value"), true),10);
  else
	value = integer2string(binary2integer(expr.get_string("value"), false),10);

  size = atoi(expr.type().get("width").c_str());
  width = log(size)/log(2);

  if (expr.type().id() == "signedbv" || expr.type().id() == "c_enum")
	result = boolector_int(boolector_ctx, atoi(value.c_str()), width);
  else if (expr.type().id() == "unsignedbv")
	result = boolector_unsigned_int(boolector_ctx, atoi(value.c_str()), width);
  else if (expr.type().id()== "fixedbv")
	result = boolector_int(boolector_ctx, atoi(value.c_str()), width);

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_shift

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_shift(const exprt &expr)
{
  assert(expr.operands().size()==2);

  BtorExp *result, *operand0, *operand1;

  if (expr.op0().id()=="constant")
	operand0 = convert_shift_constant(expr.op0());
  else
    operand0 = convert_bv(expr.op0());

  if (expr.op1().id()=="constant")
	operand1 = convert_shift_constant(expr.op1());
  else
    operand1 = convert_bv(expr.op1());

  if(expr.id()=="ashr")
    result = boolector_sra(boolector_ctx, operand0, operand1);
  else if (expr.id()=="lshr")
    result = boolector_srl(boolector_ctx, operand0, operand1);
  else if(expr.id()=="shl")
    result = boolector_sll(boolector_ctx, operand0, operand1);
  else
    assert(false);

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_with

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_with(const exprt &expr)
{
  assert(expr.operands().size()>=1);
  BtorExp *result, *array, *index, *value;

  array = convert_bv(expr.op0());
  index = convert_bv(expr.op1());
  value = convert_bv(expr.op2());

  result = boolector_write(boolector_ctx, array, index, value);

  return result;
}

/*******************************************************************
 Function: boolector_dect::convert_abs

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_abs(const exprt &expr)
{
  unsigned width;
  std::string out;

  boolbv_get_width(expr.type(), width);

  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=1)
    throw "abs takes one operand";

  const exprt &op0=expr.op0();
  static BtorExp *zero, *minus_one, *is_negative, *val_orig, *val_mul;

  out = "width: "+ width;
  if (expr.type().id()=="signedbv" || expr.type().id()=="fixedbv")
    zero = boolector_int(boolector_ctx, 0, width);
  else if (expr.type().id()=="unsignedbv")
	zero = boolector_unsigned_int(boolector_ctx, 0, width);

  minus_one = boolector_int(boolector_ctx, -1, width);

  val_orig = convert_bv(op0);

  if (expr.type().id()=="signedbv" || expr.type().id()=="fixedbv")
    is_negative = boolector_slt(boolector_ctx, val_orig, zero);

  val_mul = boolector_mul(boolector_ctx, val_orig, minus_one);

  return boolector_cond(boolector_ctx, is_negative, val_mul, val_orig);
}

/*******************************************************************
 Function: boolector_dect::convert_bitnot

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_bitnot(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::convert_bitnot

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

unsigned int boolector_dect::convert_member_name(const exprt &lhs, const exprt &rhs)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}


/*******************************************************************
 Function: boolector_dect::convert_extractbit

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_extractbit(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif
}

/*******************************************************************
 Function: boolector_dect::convert_object

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_object(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: boolector_dect::select_pointer_offset

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::select_pointer_offset(const exprt &expr)
{
  assert(expr.operands().size()==1);

  BtorExp *offset;

  offset = convert_bv(expr.op0());

  return offset;
}

/*******************************************************************
 Function: boolector_dect::convert_member

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_member(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}


/*******************************************************************
 Function: convert_invalid_pointer

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_invalid_pointer(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}

/*******************************************************************
 Function: convert_pointer_object

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_pointer_object(const exprt &expr)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

}
/*******************************************************************
 Function: boolector_dect::convert_boolector_expr

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

BtorExp* boolector_dect::convert_boolector_expr(const exprt &expr)
{
  if (expr.id() == "symbol")
	return convert_identifier(expr.get_string("identifier"), expr.type());
  else if (expr.id() == "nondet_symbol") {
	return convert_identifier("nondet$"+expr.get_string("identifier"), expr.type());
  } else if (expr.id() == "typecast")
    return convert_typecast(expr);
#if 0
  else if (expr.id() == "struct")
	return convert_struct(expr);
  else if (expr.id() == "union")
	return convert_union(expr);
#endif
  else if (expr.id() == "constant")
	return convert_constant(expr);
  else if (expr.id() == "concatenation")
	return convert_concatenation(expr);
  else if (expr.id() == "bitand" || expr.id() == "bitor" || expr.id() == "bitxor"
		|| expr.id() == "bitnand" || expr.id() == "bitnor" || expr.id() == "bitnxor")
    return convert_bitwise(expr);
  else if (expr.id() == "bitnot")
	return convert_bitnot(expr);
  else if (expr.id() == "unary-")
    return convert_unary_minus(expr);
  else if (expr.id() == "if")
    return convert_if(expr);
  else if (expr.id() == "and" || expr.id() == "or" || expr.id() == "xor")
	return convert_logical_ops(expr);
  else if (expr.id() == "not")
	return convert_logical_not(expr);
  else if (expr.id() == "=" || expr.id() == "notequal")
	return convert_equality(expr);
  else if (expr.id() == "<=" || expr.id() == "<" || expr.id() == ">="
		|| expr.id() == ">")
	return convert_rel(expr);
  else if (expr.id() == "+")
	return convert_add(expr);
  else if (expr.id() == "-")
	return convert_sub(expr);
  else if (expr.id() == "/")
	return convert_div(expr);
  else if (expr.id() == "mod")
	return convert_mod(expr);
  else if (expr.id() == "*")
	return convert_mul(expr);
  else if(expr.id()=="abs")
    return convert_abs(expr);
  else if (expr.id() == "address_of" || expr.id() == "implicit_address_of"
		|| expr.id() == "reference_to")
	return convert_pointer(expr);
  else if (expr.id() == "array_of")
	return convert_array_of(expr);
  else if (expr.id() == "index")
	return convert_index(expr);
  else if (expr.id() == "ashr" || expr.id() == "lshr" || expr.id() == "shl")
	return convert_shift(expr);
  else if (expr.id() == "with")
	return convert_with(expr);
  else if (expr.id() == "member")
	return convert_member(expr);
#if 0
  else if (expr.id() == "invalid-pointer")
	return convert_invalid_pointer(expr);
#endif
  else if (expr.id()=="zero_string")
	return convert_zero_string(expr);
  else if (expr.id() == "pointer_offset")
	return select_pointer_offset(expr);
  else if (expr.id() == "pointer_object")
	return convert_pointer_object(expr);
#if 0
  else if (expr.id() == "same-object")
	return convert_object(expr);
#endif
  else if (expr.id() == ID_string_constant) {
	  exprt tmp;
	  string2array(expr, tmp);
	return convert_boolector_expr(tmp);
  } else if (expr.id() == "extractbit")
	return convert_extractbit(expr);
  else if (expr.id() == "replication") {
	assert(expr.operands().size()==2);
  } else
	throw "convert_boolector_expr: " + expr.id_string() + " is not supported yet";
}

/*******************************************************************
 Function: boolector_dect::assign_boolector_expr

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool boolector_dect::assign_boolector_expr(const exprt expr)
{
  if (expr.op0().type().id() == "pointer" && expr.op0().type().subtype().id()=="code")
  {
	ignoring(expr);
	return false;
  }
  else if (expr.op0().type().id() == "array" && expr.op0().type().subtype().id()=="struct")
  {
	ignoring(expr);
  	return false;
  }
  else if (expr.op0().type().id() == "pointer" && expr.op0().type().subtype().id()=="symbol")
  {
	ignoring(expr);
  	return false;
  }

  return true;
}


/*******************************************************************
 Function: boolector_dect::set_to

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void boolector_dect::set_to(const exprt &expr, bool value)
{
  if(expr.type().id()!="bool")
  {
    std::string msg="prop_convt::set_to got "
                    "non-boolean expression:\n";
    msg+=expr.to_string();
    throw msg;
  }

  bool boolean=true;

  forall_operands(it, expr)
    if(it->type().id()!="bool")
    {
      boolean=false;
      break;
    }

  if(boolean && assign_boolector_expr(expr))
  {
    if(expr.id()=="not")
    {
      if(expr.operands().size()==1)
      {
        set_to(expr.op0(), !value);
        return;
      }
    }
    else
    {
      if(value)
      {
        // set_to_true

        if(expr.id()=="and")
        {
          forall_operands(it, expr)
            set_to_true(*it);

          return;
        }
        else if(expr.id()=="or")
        {
          if(expr.operands().size()>0)
          {
            bvt bv;
            bv.reserve(expr.operands().size());

            forall_operands(it, expr)
              bv.push_back(convert(*it));
            prop.lcnf(bv);
            return;
          }
        }
        else if(expr.id()=="=>")
        {
          if(expr.operands().size()==2)
          {
            bvt bv;
            bv.resize(2);
            bv[0]=prop.lnot(convert(expr.op0()));
            bv[1]=convert(expr.op1());
            prop.lcnf(bv);
            return;
          }
        }
        else if(expr.id()=="=")
        {
          if(!set_equality_to_true(expr))
            return;
        }
      }
      else
      {
        // set_to_false
        if(expr.id()=="=>") // !(a=>b)  ==  (a && !b)
        {
          if(expr.operands().size()==2)
          {
            set_to_true(expr.op0());
            set_to_false(expr.op1());
          }
        }
        else if(expr.id()=="or") // !(a || b)  ==  (!a && !b)
        {
          forall_operands(it, expr)
            set_to_false(*it);
        }
      }
    }
  }

  // fall back to convert
  prop.l_set_to(convert(expr), value);

  if (value && expr.id() == "and")
  {
	forall_operands(it, expr)
	  set_to(*it, true);
	return;
  }

  if (value && expr.is_true())
	return;


  if (expr.id() == "=" && value)
  {
    assert(expr.operands().size()==2);

    BtorExp *formula, *operand0, *operand1;

	if (assign_boolector_expr(expr))
	{

	  operand0 = convert_bv(expr.op0());
	  operand1 = convert_bv(expr.op1());

	  formula = boolector_eq(boolector_ctx, operand0, operand1);
	  boolector_assert(boolector_ctx, formula);
	  //boolector_dump_btor(boolector_ctx, btorFile, formula);
	  //boolector_dump_smt(boolector_ctx, smtFile, formula);
	}
  }
}

/*******************************************************************
 Function: boolector_dect::get_number_variables_z

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

unsigned int boolector_dect::get_number_variables_boolector(void)
{
  return number_variables_boolector;
}

