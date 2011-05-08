/*******************************************************************\

Module:

Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

\*******************************************************************/

#include <unistd.h>
#include <assert.h>

#include <i2string.h>
#include <str_getline.h>
#include <prefix.h>

#include "z3_dec.h"

/*******************************************************************\

Function: z3_dect::z3_dect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3_dect::z3_dect()
{
}

/*******************************************************************\

Function: z3_dect::~z3_dect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3_dect::~z3_dect()
{
}

/*******************************************************************\

Function: z3_dect::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt z3_dect::dec_solve()
{
  status("Solving with SMT solver Z3");

#if 0
  status(integer2string(get_number_variables_z3()) + " variables, " +
		  integer2string(get_number_vcs_z3()) + " verification conditions");
#endif

  post_process();

  return read_z3_result();
}

/*******************************************************************\

Function: z3_dect::set_encoding

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_dect::set_encoding(bool enc)
{
  set_z3_encoding(enc);
}

/*******************************************************************\

Function: z3_dect::set_ecp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_dect::set_ecp(bool ecp)
{
  set_z3_ecp(ecp);
}

/*******************************************************************\

Function: z3_dect::read_assert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void z3_dect::read_assert(std::istream &in, std::string &line)
{
}

/*******************************************************************\

Function: z3_dect::read_z3_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt z3_dect::read_z3_result()
{
  Z3_lbool result;

  result = check2_z3_properties();

  if (result==Z3_L_FALSE)
	return D_UNSATISFIABLE;
  else
	return D_SATISFIABLE;
}


/*******************************************************************
 Module:

 Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

 \*******************************************************************/

#include <assert.h>
#include <ctype.h>

#include<sstream>
#include <std_expr.h>
#include <arith_tools.h>
#include <std_types.h>
#include <config.h>
#include <i2string.h>
#include <expr_util.h>
#include <string2array.h>
#include <pointer_offset_size.h>
#include <find_symbols.h>
#include <prefix.h>
#include <solvers/flattening/boolbv_width.h>

#include <solvers/flattening/boolbv.h>
#include <solvers/flattening/boolbv_type.h>

#include "z3_conv.h"
#include "../ansi-c/c_types.h"

//#define DEBUG

/*******************************************************************
 Function: z3_convt::print_data_types

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void z3_convt::print_data_types(Z3_ast operand0, Z3_ast operand1)
{
  Z3_type_ast a, b;

  a = Z3_get_type(z3_ctx, operand0);
  std::cout << "operand0 type:" << std::endl;
  std::cout << Z3_get_symbol_string(z3_ctx,Z3_get_type_name(z3_ctx, a)) << std::endl;

  b = Z3_get_type(z3_ctx, operand1);
  std::cout << "operand1:" << std::endl;
  std::cout << Z3_get_symbol_string(z3_ctx,Z3_get_type_name(z3_ctx, b)) << std::endl;
}

/*******************************************************************
 Function: z3_convt::show_bv_size

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void z3_convt::show_bv_size(Z3_ast operand)
{
  Z3_type_ast a;

  a = Z3_get_type(z3_ctx, operand);
  std::cout << "operand type: ";
  std::cout << Z3_get_symbol_string(z3_ctx,Z3_get_type_name(z3_ctx, a)) << std::endl;
  std::cout << "operand size: ";
  std::cout << Z3_get_bv_type_size(z3_ctx, a) << std::endl;
}

/*******************************************************************
 Function: z3_convt::select_pointer

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

const typet z3_convt::select_pointer(const typet &type)
{
  if (is_ptr(type))
	return select_pointer(type.subtype());
  else
	return type;
}

/*******************************************************************
 Function: z3_convt::check_all_types

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::check_all_types(const typet &type)
{
  if (type.id()=="bool" || type.id()=="signedbv" || type.id()=="unsignedbv" ||
	  type.id()=="symbol" || type.id()=="empty" || type.id() == "fixedbv" ||
	  type.id()=="array" || type.id()=="struct" || type.id()=="pointer" ||
	  type.id()=="union" || type.id()=="code")
  {
    return true;
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::is_bv

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::is_bv(const typet &type)
{
  if (type.id()=="signedbv" || type.id()=="unsignedbv" ||
	  type.id() == "fixedbv")
    return true;

  return false;
}

/*******************************************************************
 Function: z3_convt::is_signed

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::is_signed(const typet &type)
{
  if (type.id()=="signedbv" || type.id()=="fixedbv")
    return true;

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_number

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_number(int value, u_int width, bool type)
{
  static Z3_ast number_var;
  char val[2];

  sprintf(val,"%i", value);

  if (type==false)
  {
    if (int_encoding)
	  number_var = z3_api.mk_unsigned_int(z3_ctx, atoi(val));
    else
	  number_var = Z3_mk_unsigned_int(z3_ctx, atoi(val), Z3_mk_bv_type(z3_ctx, width));
  }
  else if (type==true)
  {
    if (int_encoding)
	  number_var = z3_api.mk_int(z3_ctx, atoi(val));
	else
	  number_var = Z3_mk_int(z3_ctx, atoi(val), Z3_mk_bv_type(z3_ctx, width));
  }

  return number_var;
}

/*******************************************************************
 Function: z3_convt::set_z3_encoding

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void z3_convt::set_z3_encoding(bool enc)
{
  int_encoding = enc;
}

/*******************************************************************
 Function: z3_convt::set_z3_ecp

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void z3_convt::set_z3_ecp(bool ecp)
{
  equivalence_checking = ecp;
}

/*******************************************************************
 Function: z3_convt::check2_z3_properties

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_lbool z3_convt::check2_z3_properties(void)
{
  Z3_model m = 0;
  Z3_lbool result;
  unsigned num_constants, i;

  result = z3_api.check2(z3_ctx, Z3_L_TRUE);

  if (result == Z3_L_TRUE)
  {
	Z3_check_and_get_model(z3_ctx, &m);
	num_constants = Z3_get_model_num_constants(z3_ctx, m);

	for (i = 0; i < num_constants; i++)
	{
	  std::string variable;
	  Z3_symbol name;
	  Z3_ast app, val;

	  Z3_func_decl cnst = Z3_get_model_constant(z3_ctx, m, i);
	  name = Z3_get_decl_name(z3_ctx, cnst);
	  variable = Z3_get_symbol_string(z3_ctx, name);
      app = Z3_mk_app(z3_ctx, cnst, 0, 0);
      val = app;
      Z3_eval(z3_ctx, m, app, &val);
      map_vars.insert(std::pair<std::string, Z3_ast>(variable, val));
	}
  }

  z3_prop.map_prop_vars = map_vars;

  return result;
}

/*******************************************************************
 Function: z3_convt::is_ptr

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::is_ptr(const typet &type)
{
  return type.id()=="pointer" || type.id()=="reference";
}

/*******************************************************************
 Function: z3_convt::select_pointer_value

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::select_pointer_value(Z3_ast object, Z3_ast offset, Z3_ast &bv)
{
  bv = Z3_mk_select(z3_ctx, object, offset);
  return false;
}

/*******************************************************************
 Function: z3_convt::create_z3_array_var

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::create_array_type(const typet &type, Z3_type_ast &bv)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

  Z3_type_ast tuple_type, array_of_array_type;
  unsigned width;

  if (type.subtype().id() == "bool")
  {
	if (int_encoding)
	  bv = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), Z3_mk_bool_type(z3_ctx));
	else
	  bv = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), Z3_mk_bool_type(z3_ctx));
  }
  else if (type.subtype().id() == "fixedbv")
  {
    if(boolbv_get_width(type.subtype(), width))
	  return true;

    if (int_encoding)
	  bv  = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), Z3_mk_real_type(z3_ctx));
    else
      bv = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), Z3_mk_bv_type(z3_ctx, width));
  }
  else if (type.subtype().id() == "struct")
  {
    if (create_struct_type(type.subtype(), tuple_type))
      return true;

    if (int_encoding)
      bv  = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), tuple_type);
    else
      bv = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), tuple_type);
  }
  else if (type.subtype().id() == "array") // array of array
  {
	if (create_array_type(type.subtype(), array_of_array_type))
	  return true;

    if (int_encoding)
	  bv  = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), array_of_array_type);
    else
      bv = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), array_of_array_type);
  }
  else
  {
	if (type.subtype().id() == "pointer")
	{
      if (boolbv_get_width(type.subtype().subtype(), width))
    	return true;
	}
	else
	{
      if (boolbv_get_width(type.subtype(), width))
    	return true;
	}

    if (int_encoding)
      bv  = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), Z3_mk_int_type(z3_ctx));
    else
      bv = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), Z3_mk_bv_type(z3_ctx, width));
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::create_type

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::create_type(const typet &type, Z3_type_ast &bv)
{
  unsigned width=config.ansi_c.int_width;

  if (type.id()=="bool")
  {
	bv = Z3_mk_bool_type(z3_ctx);
  }
  else if (type.id()=="signedbv" || type.id()=="unsignedbv" || type.id()=="c_enum")
  {
    if (boolbv_get_width(type, width))
      return true;

    if (int_encoding)
      bv = Z3_mk_int_type(z3_ctx);
    else
      bv = Z3_mk_bv_type(z3_ctx, width);
  }
  else if (type.id() == "fixedbv")
  {
    if (boolbv_get_width(type, width))
      return true;

    if (int_encoding)
      bv = Z3_mk_real_type(z3_ctx);
    else
      bv = Z3_mk_bv_type(z3_ctx, width);
  }
  else if (type.id()=="array")
  {
	if (type.subtype().id()=="struct")
	{
	  if (create_struct_type(type.subtype(), bv))
		return true;

	  if (int_encoding)
	  {
		bv = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), bv);
		return false;
	  }
	  else
	  {
		bv = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), bv);
		return false;
	  }
	}
	else if (type.subtype().id()=="array")
	{
	  if (create_type(type.subtype(), bv))
		return true;

	  if (int_encoding)
	  {
		bv = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), bv);
		return false;
	  }
	  else
	  {
		bv = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), bv);
		return false;
	  }
	}
	else if (type.subtype().id()=="pointer")
	{
      if (boolbv_get_width(type.subtype().subtype(), width))
	    return true;
	}
	else
	{
      if (boolbv_get_width(type.subtype(), width))
	    return true;
	}

	if (int_encoding)
	  bv = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), Z3_mk_int_type(z3_ctx));
	else
	  bv = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), Z3_mk_bv_type(z3_ctx, width));
  }
  else if (type.id()=="struct" || type.id()=="union")
  {
	if (create_struct_type(type, bv))
	  return true;
  }
  else if (type.id()=="pointer")
  {
    if (create_pointer_type(type, bv))
      return true;
  }
  else
  {
	  return true;
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::create_struct_type

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::create_struct_type(const typet &type, Z3_type_ast &bv)
{
  Z3_symbol mk_tuple_name, *proj_names;
  std::string struct_name;
  Z3_type_ast *proj_types;
  Z3_const_decl_ast mk_tuple_decl, *proj_decls;
  u_int size_of_struct;

  const struct_typet &struct_type=to_struct_type(type);

  const struct_typet::componentst &components=
    struct_type.components();

  assert(components.size()>0);
  size_of_struct = components.size();
  proj_names = new Z3_symbol[size_of_struct];
  proj_types = new Z3_type_ast[size_of_struct];
  proj_decls = new Z3_const_decl_ast[size_of_struct];

  struct_name = type.get_string("tag");
  mk_tuple_name = Z3_mk_string_symbol(z3_ctx, struct_name.c_str());

  u_int i=0;
  for(struct_typet::componentst::const_iterator
    it=components.begin();
    it!=components.end();
    it++,i++)
  {
    proj_names[i] = Z3_mk_string_symbol(z3_ctx, it->get("name").c_str());
    if (create_type(it->type(), proj_types[i]))
      return true;
  }

  bv = Z3_mk_tuple_type(z3_ctx, mk_tuple_name, i, proj_names, proj_types, &mk_tuple_decl, proj_decls);

  delete[] proj_names;
  delete[] proj_types;
  delete[] proj_decls;

  return false;
}

/*******************************************************************
 Function: z3_convt::create_enum_type

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::create_enum_type(const typet &type, Z3_type_ast &bv)
{
  if (int_encoding)
	bv = Z3_mk_int_type(z3_ctx);
  else
	bv = Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width);

  return false;
}

/*******************************************************************
 Function: z3_convt::create_pointer_type

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
bool z3_convt::create_pointer_type(const typet &type, Z3_type_ast &bv)
{
  Z3_symbol mk_tuple_name, proj_names[2];
  Z3_type_ast proj_types[2];
  Z3_const_decl_ast mk_tuple_decl, proj_decls[2];

  mk_tuple_name = Z3_mk_string_symbol(z3_ctx, "pointer_tuple");
  proj_names[0] = Z3_mk_string_symbol(z3_ctx, "object");

  if (is_ptr(type.subtype()))
  {
	if (create_type(select_pointer(type.subtype()), proj_types[0]))
	  return true;
  }
  else if (check_all_types(type.subtype()))
  {
	if (create_type(type.subtype(), proj_types[0]))
	  return true;
  }
  else if (check_all_types(type))
  {
	if (create_type(type, proj_types[0]))
	  return true;
  }
  else
  {
	return true;
  }

  proj_names[1] = Z3_mk_string_symbol(z3_ctx, "index");

  if (int_encoding)
    proj_types[1] = Z3_mk_int_type(z3_ctx);
  else
    proj_types[1] = Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width);


  bv = Z3_mk_tuple_type(z3_ctx, mk_tuple_name, 2, proj_names, proj_types, &mk_tuple_decl, proj_decls);

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_identifier

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_identifier(const std::string &identifier, const typet &type, Z3_ast &bv)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

  Z3_type_ast type_var;
  unsigned width;

#ifdef DEBUG
  std::cout << "identifier: " << identifier.c_str() << "\n";
#endif

  if (type.id()=="bool")
  {
	bv = z3_api.mk_bool_var(z3_ctx, identifier.c_str());
  }
  else if (type.id()=="signedbv" || type.id()=="unsignedbv")
  {
    if (boolbv_get_width(type, width))
      return true;

	if (int_encoding)
      bv = z3_api.mk_int_var(z3_ctx, identifier.c_str());
	else
	  bv = z3_api.mk_var(z3_ctx, identifier.c_str(), Z3_mk_bv_type(z3_ctx, width));
  }
  else if (type.id()== "fixedbv")
  {
    if (boolbv_get_width(type, width))
      return true;

	if (int_encoding)
	  bv = z3_api.mk_real_var(z3_ctx, identifier.c_str());
	else
	  bv = z3_api.mk_var(z3_ctx, identifier.c_str(), Z3_mk_bv_type(z3_ctx, width));
  }
  else if (type.id()=="array")
  {
    if (create_array_type(type, type_var))
      return true;

    bv = z3_api.mk_var(z3_ctx, identifier.c_str(), type_var);
  }
  else if (type.id()=="pointer")
  {
	if (create_pointer_type(type, type_var))
	  return true;

	bv = z3_api.mk_var(z3_ctx, identifier.c_str(), type_var);
  }
  else if (type.id()=="struct" || type.id()=="union")
  {
	if (create_struct_type(type, type_var))
	  return true;

	bv = z3_api.mk_var(z3_ctx, identifier.c_str(), type_var);
  }
  else if (type.id()=="c_enum")
  {
	if (create_enum_type(type, type_var))
	  return true;

	bv = z3_api.mk_var(z3_ctx, identifier.c_str(), type_var);
  }
  else
	throw "convert_identifier: " + type.id_string() + " is unsupported";

  ++number_variables_z3;

  return false;
}

/*******************************************************************\

Function: z3_convt::is_in_cache
  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool z3_convt::is_in_cache(const exprt &expr)
{
  bv_cachet::const_iterator cache_result=bv_cache.find(expr);
  if(cache_result!=bv_cache.end())
  {
    //std::cout << "Cache hit on " << expr.pretty() << "\n";
    return true;
  }

  return false;
}

/*******************************************************************\

Function: z3_convt::convert_bv
  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool z3_convt::convert_bv(const exprt &expr, Z3_ast &bv)
{
  bv_cachet::const_iterator cache_result=bv_cache.find(expr);
  if(cache_result!=bv_cache.end())
  {
    //std::cout << "Cache hit on " << expr.pretty() << "\n";
    bv = cache_result->second;
    return false;
  }

  if (convert_z3_expr(expr, bv))
    return true;

  // insert into cache
  bv_cache.insert(std::pair<const exprt, Z3_ast>(expr, bv));

  return false;
}

/*******************************************************************
 Function: z3_convt::read_cache

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::read_cache(const exprt &expr, Z3_ast &bv)
{
  std::string symbol;

  symbol = expr.get_string("identifier");

  for(z3_cachet::const_iterator it = z3_cache.begin();
  it != z3_cache.end(); it++)
  {
	if (symbol.compare((*it).second.c_str())==0)
	{
	  //std::cout << "Cache hit on:" << (*it).first.pretty() << "\n";
	  if (convert_bv((*it).first, bv))
	    return true;

	  return false;
	}
  }

  if (convert_bv(expr, bv))
	return true;

  return false;
}

/*******************************************************************
 Function: z3_convt::write_cache

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::write_cache(const exprt &expr)
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
      z3_cache.insert(std::pair<const exprt, std::string>(expr, symbol));
      return false;
	}
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_lt

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_lt(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static Z3_ast bv, operand[2];
  const exprt &op0=expr.op0();
  const exprt &op1=expr.op1();

  if (convert_bv(op0, operand[0]))
	return Z3_mk_false(z3_ctx);
  if (convert_bv(op1, operand[1]))
	return Z3_mk_false(z3_ctx);

  if (op0.type().id() == "pointer")
	operand[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 1);

  if (op1.type().id() == "pointer")
    operand[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 1);

  if (op0.id() == "typecast" && op0.type().id()=="signedbv")
  {
	const exprt &object=expr.op0().operands()[0];
	std::string value;
	unsigned width;

	if (op1.id()=="constant" && object.type().id()=="unsignedbv")
	{
	  value = integer2string(binary2integer(expr.op1().get_string("value"), false),10);

      if (boolbv_get_width(expr.op1().type(), width))
	    return Z3_mk_false(z3_ctx);

      operand[1] = convert_number(atoi(value.c_str()), width, false);
      bv = Z3_mk_bvult(z3_ctx, operand[0], operand[1]);

	  return bv;
	}
  }

  if (int_encoding)
  {
    bv = Z3_mk_lt(z3_ctx, operand[0], operand[1]);
  }
  else
  {
    if (op1.type().id()=="signedbv" || op1.type().id()=="fixedbv"
     || op1.type().id()=="pointer")
      bv = Z3_mk_bvslt(z3_ctx, operand[0], operand[1]);
    else if (op1.type().id()=="unsignedbv")
      bv = Z3_mk_bvult(z3_ctx, operand[0], operand[1]);
  }

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_gt

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
Z3_ast z3_convt::convert_gt(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static Z3_ast bv, operand[2];

  if (convert_bv(expr.op0(), operand[0]))
	return Z3_mk_false(z3_ctx);
  if (convert_bv(expr.op1(), operand[1]))
	return Z3_mk_false(z3_ctx);

  if (expr.op0().type().id() == "pointer")
	operand[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 1);

  if (expr.op1().type().id() == "pointer")
    operand[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 1);

  //workaround: bug in the front-end
  //to check it, run example ex10.c of NEC
  if (expr.op0().id() == "typecast" && expr.op0().type().id()=="signedbv")
  {
	const exprt &object=expr.op0().operands()[0];
	std::string value;
	unsigned width;

	if (expr.op1().id()=="constant" && object.type().id()=="unsignedbv")
	{
	  value = integer2string(binary2integer(expr.op1().get_string("value"), false),10);

      if (boolbv_get_width(expr.op1().type(), width))
	    return Z3_mk_false(z3_ctx);

      operand[1] = convert_number(atoi(value.c_str()), width, false);
      bv = Z3_mk_bvugt(z3_ctx, operand[0], operand[1]);

	  return bv;
	}
  }

  if (int_encoding)
  {
    bv = Z3_mk_gt(z3_ctx, operand[0], operand[1]);
  }
  else
  {
    if (expr.op1().type().id()=="signedbv" || expr.op1().type().id()=="fixedbv"
  	  || expr.op1().type().id()=="pointer")
      bv = Z3_mk_bvsgt(z3_ctx, operand[0], operand[1]);
    else if (expr.op1().type().id()=="unsignedbv")
  	  bv = Z3_mk_bvugt(z3_ctx, operand[0], operand[1]);
  }

  return bv;
}


/*******************************************************************
 Function: z3_convt::convert_le

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_le(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static Z3_ast bv, operand[2];

  if (convert_bv(expr.op0(), operand[0]))
	return Z3_mk_false(z3_ctx);
  if (convert_bv(expr.op1(), operand[1]))
	return Z3_mk_false(z3_ctx);

  if (expr.op0().type().id() == "pointer")
	operand[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 1);

  if (expr.op1().type().id() == "pointer")
    operand[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 1);

  if (expr.op0().id() == "typecast" && expr.op0().type().id()=="signedbv")
  {
	const exprt &object=expr.op0().operands()[0];
	std::string value;
	unsigned width;

	if (expr.op1().id()=="constant" && object.type().id()=="unsignedbv")
	{
	  value = integer2string(binary2integer(expr.op1().get_string("value"), false),10);

      if (boolbv_get_width(expr.op1().type(), width))
	    return Z3_mk_false(z3_ctx);

      operand[1] = convert_number(atoi(value.c_str()), width, false);
      bv = Z3_mk_bvule(z3_ctx, operand[0], operand[1]);

	  return bv;
	}
  }

  if (int_encoding)
  {
    bv = Z3_mk_le(z3_ctx, operand[0], operand[1]);
  }
  else
  {
    if (expr.op1().type().id()=="signedbv" || expr.op1().type().id()=="fixedbv"
    	|| expr.op1().type().id()=="pointer")
  	  bv = Z3_mk_bvsle(z3_ctx, operand[0], operand[1]);
    else if (expr.op1().type().id()=="unsignedbv")
  	  bv = Z3_mk_bvule(z3_ctx, operand[0], operand[1]);
  }

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_ge

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_ge(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static Z3_ast bv, operand[2];

  if (convert_bv(expr.op0(), operand[0]))
	return Z3_mk_false(z3_ctx);
  if (convert_bv(expr.op1(), operand[1]))
	return Z3_mk_false(z3_ctx);

  if (expr.op0().type().id() == "pointer")
	operand[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 1);

  if (expr.op1().type().id() == "pointer")
    operand[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 1);

  if (expr.op0().id() == "typecast" && expr.op0().type().id()=="signedbv")
  {
	const exprt &object=expr.op0().operands()[0];
	std::string value;
	unsigned width;

	if (expr.op1().id()=="constant" && object.type().id()=="unsignedbv")
	{
	  value = integer2string(binary2integer(expr.op1().get_string("value"), false),10);

      if (boolbv_get_width(expr.op1().type(), width))
	    return Z3_mk_false(z3_ctx);

      operand[1] = convert_number(atoi(value.c_str()), width, false);
      bv = Z3_mk_bvuge(z3_ctx, operand[0], operand[1]);

	  return bv;
	}
  }

  if (int_encoding)
  {
    bv = Z3_mk_ge(z3_ctx, operand[0], operand[1]);
  }
  else
  {
    if (expr.op1().type().id()=="signedbv" || expr.op1().type().id()=="fixedbv"
			|| expr.op1().type().id()=="pointer")
  	  bv = Z3_mk_bvsge(z3_ctx, operand[0], operand[1]);
    else if (expr.op1().type().id()=="unsignedbv")
  	  bv = Z3_mk_bvuge(z3_ctx, operand[0], operand[1]);
  }

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_eq

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_eq(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static Z3_ast bv, operand[2];
  const exprt &op0=expr.op0();
  const exprt &op1=expr.op1();

  if (op0.type().id()=="array")
  {
    if (write_cache(op0))
      return Z3_mk_false(z3_ctx);
  }

  if (convert_bv(op0, operand[0]))
	return Z3_mk_false(z3_ctx);

  if (convert_bv(op1, operand[1]))
	return Z3_mk_false(z3_ctx);

  if (op0.type().id()=="pointer" && op1.type().id()=="pointer")
  {
    static Z3_ast pointer[2], formula[2];

	pointer[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 0);
	pointer[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 0);

    if (expr.id() == "=")
	  formula[0] = Z3_mk_eq(z3_ctx, pointer[0], pointer[1]);
    else
      formula[0] = Z3_mk_distinct(z3_ctx, 2, pointer);

    pointer[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 1);
    pointer[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 1);

	if (expr.id() == "=")
	  formula[1] = Z3_mk_eq(z3_ctx, pointer[0], pointer[1]);
	else
	  formula[1] = Z3_mk_distinct(z3_ctx, 2, pointer);

	bv = Z3_mk_and(z3_ctx, 2, formula);

	return bv;
  }
  else
  {
    if (expr.id() == "=")
      bv = Z3_mk_eq(z3_ctx, operand[0], operand[1]);
    else
	  bv = Z3_mk_distinct(z3_ctx, 2, operand);
  }

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_invalid

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_invalid(const exprt &expr)
{
  assert(expr.operands().size()==1);
  static Z3_ast bv, pointer, operand[2];

  if (!is_in_cache(expr.op0()) && expr.op0().id()=="typecast")
	return Z3_mk_true(z3_ctx);

  if (convert_z3_expr(expr.op0(), pointer)); //return pointer tuple
    return Z3_mk_false(z3_ctx);

  if (expr.op0().type().id()=="pointer")
	  operand[0] = z3_api.mk_tuple_select(z3_ctx, pointer, 1); //pointer index

  operand[1] = convert_number(0, config.ansi_c.int_width, true);

  if (int_encoding)
    bv = Z3_mk_ge(z3_ctx, operand[0], operand[1]);
  else
    bv = Z3_mk_bvsge(z3_ctx, operand[0], operand[1]);

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_same_object

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_same_object(const exprt &expr)
{
  const exprt::operandst &operands=expr.operands();
  static Z3_ast bv, operand[2], formula[2], pointer[2];
  const exprt &op0=expr.op0();
  const exprt &op1=expr.op1();

  if ((is_in_cache(op0) && !is_in_cache(op1))
	  || (!is_in_cache(op0) && !is_in_cache(op1)))
  {
	//object is not in the cache and generates spurious counter-example
    return Z3_mk_false(z3_ctx);
  }
  else if (op0.id()=="address_of" && op1.id()=="constant")
  {
	return Z3_mk_false(z3_ctx); //TODO
  }
  else if (operands.size()==2 &&
     is_ptr(operands[0].type()) &&
     is_ptr(operands[1].type()))
  {
	if (convert_bv(op0, pointer[0]))
	  return Z3_mk_false(z3_ctx);
	if (convert_bv(op1, pointer[1]))
	  return Z3_mk_false(z3_ctx);

	operand[0] = z3_api.mk_tuple_select(z3_ctx, pointer[0], 0);
	operand[1] = z3_api.mk_tuple_select(z3_ctx, pointer[1], 0);

	formula[0] = Z3_mk_eq(z3_ctx, operand[0], operand[1]);

	operand[0] = z3_api.mk_tuple_select(z3_ctx, pointer[0], 1);
	operand[1] = z3_api.mk_tuple_select(z3_ctx, pointer[1], 1);

	formula[1] = Z3_mk_eq(z3_ctx, operand[0], operand[1]);
	bv = Z3_mk_and(z3_ctx, 2, formula);
  }

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_dynamic_object

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_dynamic_object(const exprt &expr)
{
  //TODO: understand how to create a formula to "is_dynamic_object"
  //This is wrong. As a consequence, we do not find bugs related to dynamic memory allocation
  assert(expr.operands().size()==1);
  static Z3_ast bv, operand;

  if (convert_bv(expr.op0(), operand))
	return Z3_mk_false(z3_ctx);

  bv = Z3_mk_true(z3_ctx);

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_overflow_sum

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_overflow_sum(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static Z3_ast bv, result[2], operand[2];

  if (expr.op0().type().id()=="array")
  {
    if (write_cache(expr.op0()))
      return Z3_mk_false(z3_ctx);
  }

  if (convert_bv(expr.op0(), operand[0]))
	return Z3_mk_false(z3_ctx);;

  if (expr.op0().type().id()=="pointer")
	operand[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 1);

  if (convert_bv(expr.op1(), operand[1]))
    return Z3_mk_false(z3_ctx);;

  if (expr.op1().type().id()=="pointer")
	operand[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 1);

  if (expr.op0().type().id()=="signedbv" && expr.op1().type().id()=="signedbv")
    result[0] = Z3_mk_bvadd_no_overflow(z3_ctx, operand[0], operand[1], 1);
  else if (expr.op0().type().id()=="unsignedbv" && expr.op1().type().id()=="unsignedbv")
	result[0] = Z3_mk_bvadd_no_overflow(z3_ctx, operand[0], operand[1], 0);

  result[1] = Z3_mk_bvadd_no_underflow(z3_ctx, operand[0], operand[1]);
  bv = Z3_mk_not(z3_ctx, Z3_mk_and(z3_ctx, 2, result));

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_overflow_sub

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_overflow_sub(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static Z3_ast bv, result[2], operand[2];

  if (expr.op0().type().id()=="array")
  {
    if (write_cache(expr.op0()))
      return Z3_mk_false(z3_ctx);;
  }

  if (convert_bv(expr.op0(), operand[0]))
	return Z3_mk_false(z3_ctx);;

  if (expr.op0().type().id()=="pointer")
	operand[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 1);

  if (convert_bv(expr.op1(), operand[1]))
	return Z3_mk_false(z3_ctx);;

  if (expr.op1().type().id()=="pointer")
	operand[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 1);

  if (expr.op0().type().id()=="signedbv" && expr.op1().type().id()=="signedbv")
    result[1] = Z3_mk_bvsub_no_underflow(z3_ctx, operand[0], operand[1], 1);
  else if (expr.op0().type().id()=="unsignedbv" && expr.op1().type().id()=="unsignedbv")
	result[1] = Z3_mk_bvsub_no_underflow(z3_ctx, operand[0], operand[1], 0);

  result[0] = Z3_mk_bvsub_no_overflow(z3_ctx, operand[0], operand[1]);
  bv = Z3_mk_not(z3_ctx, Z3_mk_and(z3_ctx, 2, result));

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_overflow_mul

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_overflow_mul(const exprt &expr)
{
  assert(expr.operands().size()==2);
  static Z3_ast bv, operand[2];

  if (expr.op0().type().id()=="array")
  {
    if (write_cache(expr.op0()))
      return Z3_mk_false(z3_ctx);;
  }

  if (convert_bv(expr.op0(), operand[0]))
	return Z3_mk_false(z3_ctx);;

  if (expr.op0().type().id()=="pointer")
	operand[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 1);

  if (convert_bv(expr.op1(), operand[1]))
	return Z3_mk_false(z3_ctx);;

  if (expr.op1().type().id()=="pointer")
	operand[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 1);

  if (expr.op0().type().id()=="signedbv" && expr.op1().type().id()=="signedbv")
    bv = Z3_mk_not(z3_ctx, Z3_mk_bvmul_no_overflow(z3_ctx, operand[0], operand[1], 1));
  else if (expr.op0().type().id()=="unsignedbv" && expr.op1().type().id()=="unsignedbv")
	bv = Z3_mk_not(z3_ctx, Z3_mk_bvmul_no_overflow(z3_ctx, operand[0], operand[1], 0));

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_overflow_unary

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_overflow_unary(const exprt &expr)
{
  assert(expr.operands().size()==1);
  static Z3_ast bv, operand;

  if (convert_bv(expr.op0(), operand))
	return Z3_mk_false(z3_ctx);;

  if (expr.op0().type().id()=="pointer")
	operand = z3_api.mk_tuple_select(z3_ctx, operand, 1);

  bv = Z3_mk_not(z3_ctx, Z3_mk_bvneg_no_overflow(z3_ctx, operand));

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_overflow_typecast

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_overflow_typecast(const exprt &expr)
{
  unsigned bits=atoi(expr.id().c_str()+18);

  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=1)
    throw "operand "+expr.id_string()+" takes one operand";

  static Z3_ast bv, operand[3], mid, overflow[2], tmp, minus_one, two;
  u_int i, result=1, width;
  std::string value;

  if (boolbv_get_width(expr.op0().type(), width))
    return Z3_mk_false(z3_ctx);

  if(bits>=width || bits==0)
    throw "overflow-typecast got wrong number of bits";

  assert(bits <= 32);

  for(i = 0; i < bits; i++)
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

  if (convert_bv(expr.op0(), operand[0]))
	return Z3_mk_false(z3_ctx);

  if (expr.op0().type().id()=="signedbv" || expr.op0().type().id()=="fixedbv")
  {
	tmp = convert_number(result, width, true);
	two = convert_number(2, width, true);
	minus_one = convert_number(-1, width, true);
	mid = Z3_mk_bvsdiv(z3_ctx, tmp, two);
	operand[1] = Z3_mk_bvsub(z3_ctx, mid, minus_one);
	operand[2] = Z3_mk_bvmul(z3_ctx, operand[1], minus_one);

	overflow[0] = Z3_mk_bvslt(z3_ctx, operand[0], operand[1]);
	overflow[1] = Z3_mk_bvsgt(z3_ctx, operand[0], operand[2]);
	bv = Z3_mk_not(z3_ctx, Z3_mk_and(z3_ctx, 2, overflow));
  }
  else if (expr.op0().type().id()=="unsignedbv")
  {
	operand[2] = convert_number(0, width, false);
	operand[1] = convert_number(result, width, false);
	overflow[0] = Z3_mk_bvult(z3_ctx, operand[0], operand[1]);
	overflow[1] = Z3_mk_bvugt(z3_ctx, operand[0], operand[2]);
	bv = Z3_mk_not(z3_ctx, Z3_mk_and(z3_ctx, 2, overflow));
  }

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_rest_member

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_rest_member(const exprt &expr)
{
  Z3_ast bv;

  if (convert_bv(expr,bv))
	return Z3_mk_false(z3_ctx);

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_rest_index

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

Z3_ast z3_convt::convert_rest_index(const exprt &expr)
{
  //TODO: understand how to create a formula to "index"

  Z3_ast bv, operand0, operand1;

  if (expr.operands().size()!=2)
    throw "index takes two operands";

  const exprt &array=expr.op0();
  const exprt &index=expr.op1();

  if (convert_bv(array, operand0))
	return Z3_mk_false(z3_ctx);

  if (convert_bv(index, operand1))
	return Z3_mk_false(z3_ctx);

  bv = Z3_mk_select(z3_ctx, operand0, operand1);

  return bv;
}

/*******************************************************************
 Function: z3_convt::convert_rest

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

literalt z3_convt::convert_rest(const exprt &expr)
{
  literalt l = z3_prop.new_variable();
  static Z3_ast formula, constraint;

  if (!assign_z3_expr(expr) && !ignoring_expr)
	return l;

  if (expr.id() == "<")
	constraint = convert_lt(expr);
  else if (expr.id() == ">")
	constraint = convert_gt(expr);
  else if (expr.id() == "<=")
	constraint = convert_le(expr);
  else if (expr.id() == ">=")
    constraint = convert_ge(expr);
  else if (expr.id() == "=" || expr.id() == "notequal")
	constraint = convert_eq(expr);
  else if (expr.id() == "invalid-pointer")
	constraint = convert_invalid(expr);
  else if (expr.id() == "same-object")
	constraint = convert_same_object(expr);
  else if (expr.id() == "is_dynamic_object")
	//ignoring(expr);
	constraint = convert_dynamic_object(expr);
  else if (expr.id() == "overflow-+" && !int_encoding)
	constraint = convert_overflow_sum(expr);
  else if (expr.id() == "overflow--" && !int_encoding)
	constraint = convert_overflow_sub(expr);
  else if (expr.id() == "overflow-*" && !int_encoding)
	constraint = convert_overflow_mul(expr);
  else if (expr.id() == "overflow-unary-" && !int_encoding)
	constraint = convert_overflow_unary(expr);
  else if(has_prefix(expr.id_string(), "overflow-typecast-") && !int_encoding)
	constraint = convert_overflow_typecast(expr);
  else if (expr.id() == "member")
	constraint = convert_rest_member(expr);
  else if (expr.id() == "index")
	ignoring(expr);
	//constraint = convert_rest_index(expr); //TODO
  else if (expr.id()=="pointer_object_has_type")
	ignoring(expr);
  else if (expr.id() == "is_zero_string")
  {
	ignoring(expr);
	return l;
  }
  else
	throw "convert_z3_expr: " + expr.id_string() + " is unsupported";

  formula = Z3_mk_iff(z3_ctx, z3_prop.z3_literal(l), constraint);
  Z3_assert_cnstr(z3_ctx, formula);

  ++number_vcs_z3;
  ++number_variables_z3;

  return l;
}

/*******************************************************************
 Function: z3_convt::convert_rel

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_rel(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==2);

  Z3_ast operand0, operand1;

  if (convert_bv(expr.op0(), operand0))
	return true;
  if (convert_bv(expr.op1(), operand1))
	return true;

  if (expr.op0().type().id() == "pointer")
    operand0 = z3_api.mk_tuple_select(z3_ctx, operand0, 1); //select pointer index

  if (expr.op1().type().id() == "pointer")
    operand1 = z3_api.mk_tuple_select(z3_ctx, operand1, 1); //select pointer index

  const typet &op_type=expr.op0().type();

  if (int_encoding)
  {
    if(expr.id()=="<=")
   	  bv = Z3_mk_le(z3_ctx,operand0,operand1);
    else if(expr.id()=="<")
      bv = Z3_mk_lt(z3_ctx,operand0,operand1);
    else if(expr.id()==">=")
      bv = Z3_mk_ge(z3_ctx,operand0,operand1);
    else if(expr.id()==">")
      bv = Z3_mk_gt(z3_ctx,operand0,operand1);
  }
  else
  {
    if (op_type.id()=="unsignedbv" || op_type.subtype().id()=="unsignedbv"
    	|| op_type.subtype().id()=="symbol")
    {
      if(expr.id()=="<=")
   	    bv = Z3_mk_bvule(z3_ctx,operand0,operand1);
      else if(expr.id()=="<")
        bv = Z3_mk_bvult(z3_ctx,operand0,operand1);
      else if(expr.id()==">=")
        bv = Z3_mk_bvuge(z3_ctx,operand0,operand1);
      else if(expr.id()==">")
        bv = Z3_mk_bvugt(z3_ctx,operand0,operand1);
    }
    else if (op_type.id()=="signedbv" || op_type.id()=="fixedbv" ||
			 op_type.subtype().id()=="signedbv" || op_type.subtype().id()=="fixedbv")
    {
      if(expr.id()=="<=")
        bv = Z3_mk_bvsle(z3_ctx,operand0,operand1);
      else if(expr.id()=="<")
        bv = Z3_mk_bvslt(z3_ctx,operand0,operand1);
      else if(expr.id()==">=")
        bv = Z3_mk_bvsge(z3_ctx,operand0,operand1);
      else if(expr.id()==">")
        bv = Z3_mk_bvsgt(z3_ctx,operand0,operand1);
    }
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_typecast

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_typecast(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==1);
  const exprt &op=expr.op0();

  Z3_ast args[2];

  if (convert_bv(op, bv))
	return true;

  if(expr.type().id()=="bool")
  {
    if(op.type().id()=="signedbv" ||
       op.type().id()=="unsignedbv" ||
       op.type().id()=="pointer")
    {
      args[0] = bv;
   	  if (int_encoding)
    	args[1] = z3_api.mk_int(z3_ctx, 0);
      else
    	args[1] = Z3_mk_int(z3_ctx, 0, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width));

   	  bv = Z3_mk_distinct(z3_ctx,2,args);
    }
    else
    {
      throw "TODO typecast1 "+op.type().id_string()+" -> bool";
    }
  }
  else if ((expr.type().id()=="signedbv" || expr.type().id()=="unsignedbv"
	  || expr.type().id()=="fixedbv" || expr.type().id()=="pointer")
	  && op.type().subtype().id()!="symbol" && expr.type().subtype().id()!="symbol")
  {
	  unsigned to_width;

      if (expr.type().id()=="pointer" && expr.type().subtype().id()!="empty")
      {
   	    if (boolbv_get_width(expr.type().subtype(), to_width))
    	  return true;
      }
      else if (expr.type().id()=="pointer" && expr.type().subtype().id()=="empty")
      {
    	to_width=config.ansi_c.int_width;
      }
      else
      {
     	if (boolbv_get_width(expr.type(), to_width))
      	  return true;
      }

    //std::cout << "to_width: " << to_width << "\n";

    if (op.type().id()=="signedbv" || op.type().id()=="fixedbv" ||
    	op.type().subtype().id()=="signedbv" || op.type().subtype().id()=="fixedbv")
    {
      unsigned from_width;

      if (op.type().id()=="pointer")
      {
       	if (boolbv_get_width(op.type().subtype(), from_width))
        	  return true;
      }
      else
      {
       	if (boolbv_get_width(op.type(), from_width))
       	  return true;
      }

      if(from_width==to_width)
      {
    	if (convert_bv(op, bv))
    	  return true;

        if (op.type().id()=="pointer")
          bv = z3_api.mk_tuple_select(z3_ctx, bv, 0);
      }
      else if(from_width<to_width)
      {
    	  if (convert_bv(op, args[0]))
    		return true;

          if (op.type().id()=="pointer")
    	    args[0] = z3_api.mk_tuple_select(z3_ctx, args[0], 0);

          if (int_encoding)
        	bv=args[0];
          else
    	    bv = Z3_mk_sign_ext(z3_ctx, (to_width-from_width), args[0]);
      }
      else if (from_width>to_width)
      {
    	if (convert_bv(op, args[0]))
    	  return true;

        if (op.type().id()=="pointer")
  	      args[0] = z3_api.mk_tuple_select(z3_ctx, args[0], 0);

        if (int_encoding)
      	  bv=args[0];
        else
    	  bv = Z3_mk_extract(z3_ctx, (to_width-1), 0, args[0]);
      }
    }
    else if (op.type().id()=="unsignedbv" || op.type().subtype().id()=="unsignedbv")
    {
      unsigned from_width;

      if (op.type().id()=="pointer")
      {
       	if (boolbv_get_width(op.type().subtype(), from_width))
        	  return true;
      }
      else
      {
       	if (boolbv_get_width(op.type(), from_width))
       	  return true;
      }

      if(from_width==to_width)
      {
    	if (convert_bv(op, bv))
    	  return true;

        if (op.type().id()=="pointer")
          bv = z3_api.mk_tuple_select(z3_ctx, bv, 0);
      }
      else if(from_width<to_width)
      {
    	//std::cout << "to_width-from_width: " << to_width-from_width << "\n";
    	if (convert_bv(op, args[0]))
    	  return true;

        if (op.type().id()=="pointer")
  	      args[0] = z3_api.mk_tuple_select(z3_ctx, args[0], 0);

        if (int_encoding)
          bv=args[0];
        else
    	  bv = Z3_mk_zero_ext(z3_ctx, (to_width-from_width), args[0]);
      }
      else if (from_width>to_width)
      {
      	if (convert_bv(op, args[0]))
      	  return true;

        if (op.type().id()=="pointer")
  	      args[0] = z3_api.mk_tuple_select(z3_ctx, args[0], 0);

        if (int_encoding)
      	  bv=args[0];
        else
          bv = Z3_mk_extract(z3_ctx, (to_width-1), 0, args[0]);
      }
    }
    else if (op.type().id()=="bool")
	{
      Z3_ast zero=0, one=0;
      unsigned width;

      if (boolbv_get_width(expr.type(), width))
        return true;

	  if (expr.type().id()=="signedbv" || expr.type().id()=="fixedbv")
	  {
	    zero = convert_number(0, width, true);
	    one =  convert_number(1, width, true);
	  }
	  else if (expr.type().id()=="unsignedbv")
	  {
		zero = convert_number(0, width, false);
		one =  convert_number(1, width, false);
	  }
	  bv = Z3_mk_ite(z3_ctx, bv, one, zero);
	}
    else if(op.type().subtype().id()=="empty")
    {
      unsigned from_width=config.ansi_c.int_width;
      Z3_ast object;

      if(from_width==to_width)
      {
        //new change
    	if (convert_bv(op, args[0]))
    	  return true;

    	bv = z3_api.mk_tuple_select(z3_ctx, args[0], 0);
      }
      else if(from_width<to_width)
      {
    	if (convert_bv(op, args[0]))
    	  return true;

    	object = z3_api.mk_tuple_select(z3_ctx, args[0], 0);

        if (int_encoding)
      	  bv=args[0];
        else
    	  bv = Z3_mk_sign_ext(z3_ctx, (to_width-from_width), object);
      }
      else if (from_width>to_width)
      {
    	if ( convert_bv(op, args[0]))
    	  return true;

    	object = z3_api.mk_tuple_select(z3_ctx, args[0], 0);

        if (int_encoding)
      	  bv=args[0];
        else
    	  bv = Z3_mk_extract(z3_ctx, (to_width-1), 0, object);
      }
    }
    else
    {
      return true;
    }
    if (expr.type().id()=="pointer")
    {
      Z3_ast pointer_var;

      if (convert_z3_pointer(expr, "pointer", pointer_var))
    	return true;

      bv = z3_api.mk_tuple_update(z3_ctx, pointer_var, 0, bv);
    }
  }

  if(expr.type().id()=="c_enum")
  {
	Z3_ast zero, one;
	unsigned width;

	if (op.type().id()=="bool")
	{
      if (boolbv_get_width(expr.type(), width))
        return true;

	  zero = convert_number(0, width, true);
	  one =  convert_number(1, width, true);
	  bv = Z3_mk_ite(z3_ctx, bv, one, zero);
	}
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_struct

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_struct(const exprt &expr, Z3_ast &bv)
{
  Z3_ast value;

  const struct_typet &struct_type=to_struct_type(expr.type());
  const struct_typet::componentst &components=struct_type.components();
  u_int i=0;

  assert(components.size()==expr.operands().size());

  if (convert_identifier(expr.type().get_string("tag"), expr.type(), bv))
	return true;

  for(struct_typet::componentst::const_iterator
    it=components.begin();
    it!=components.end();
    it++, i++)
  {
    if (convert_bv(expr.operands()[i], value))
      return true;

    bv = z3_api.mk_tuple_update(z3_ctx, bv, i, value);
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_z3_pointer

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_z3_pointer(const exprt &expr, std::string symbol, Z3_ast &bv)
{
  Z3_type_ast tuple_type;
  std::string cte, identifier;
  unsigned width;
  char val[2];

  if (check_all_types(expr.type().subtype()))
  {
	if (expr.type().subtype().id()=="pointer")
	{
      if (boolbv_get_width(expr.type().subtype().subtype(), width))
        return true;
	}
	else
	{
      if (boolbv_get_width(expr.type().subtype(), width))
        return true;
	}

    if (create_pointer_type(expr.type().subtype(), tuple_type))
      return true;
  }
  else if (check_all_types(expr.type()))
  {
    if (boolbv_get_width(expr.type(), width))
      return true;

	if (create_pointer_type(expr.type(), tuple_type))
	  return true;
  }

  sprintf(val,"%i", width);
  identifier = symbol;
  identifier += val;
  bv = z3_api.mk_var(z3_ctx, identifier.c_str(), tuple_type);

  if (expr.get("value").compare("NULL") == 0)
  {
    if (int_encoding)
      bv = z3_api.mk_tuple_update(z3_ctx, bv, 1, z3_api.mk_int(z3_ctx,-1));
    else
      bv = z3_api.mk_tuple_update(z3_ctx, bv, 1, Z3_mk_int(z3_ctx, -1, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width)));
  }
  else
  {
    if (int_encoding)
      bv = z3_api.mk_tuple_update(z3_ctx, bv, 1, z3_api.mk_int(z3_ctx, 0));
    else
      bv = z3_api.mk_tuple_update(z3_ctx, bv, 1, Z3_mk_int(z3_ctx, 0, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width)));
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_zero_string

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_zero_string(const exprt &expr, Z3_ast &bv)
{
  Z3_type_ast array_type;

  if (create_array_type(expr.type(), array_type))
	return true;

  bv = z3_api.mk_var(z3_ctx, "zero_string", array_type);

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_array

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_array(const exprt &expr, Z3_ast &bv)
{
  u_int width=0, i=0;
  Z3_type_ast array_type, tuple_type;
  Z3_ast array_cte, int_cte, val_cte, tmp_struct;
  std::string value_cte;
  char i_str[2];

  width = config.ansi_c.int_width;

  if (expr.type().subtype().id() == "fixedbv")
  {
    if (boolbv_get_width(expr.type().subtype(), width))
      return true;

    if (int_encoding)
      array_type  = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), Z3_mk_real_type(z3_ctx));
    else
      array_type  = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), Z3_mk_bv_type(z3_ctx, width));
  }
  else if (expr.type().subtype().id() == "struct")
  {
    if (create_struct_type(expr.op0().type(), tuple_type))
      return true;

    if (int_encoding)
      array_type  = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), tuple_type);
    else
      array_type = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), tuple_type);

    value_cte = "constant" + expr.op0().type().get_string("tag");
    array_cte = z3_api.mk_var(z3_ctx, value_cte.c_str(), array_type);

    i=0;
    forall_operands(it, expr)
    {
  	sprintf(i_str,"%i",i);
  	if (int_encoding)
  	  int_cte = z3_api.mk_int(z3_ctx, atoi(i_str));
  	else
  	  int_cte = Z3_mk_int(z3_ctx, atoi(i_str), Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width));

  	if (convert_struct(*it, tmp_struct))
  	  return true;

  	Z3_mk_store(z3_ctx, array_cte, int_cte, tmp_struct);
  	++i;
    }

    return array_cte;
  }
  else if (expr.type().subtype().id() == "array")
  {
    if (boolbv_get_width(expr.type().subtype().subtype(), width))
      return true;

	if (create_array_type(expr.type(), array_type))
	  return true;
  }
  else
  {
    if (boolbv_get_width(expr.type().subtype(), width))
      return true;

    if (int_encoding)
      array_type  = Z3_mk_array_type(z3_ctx, Z3_mk_int_type(z3_ctx), Z3_mk_int_type(z3_ctx));
    else
	  array_type  = Z3_mk_array_type(z3_ctx, Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width), Z3_mk_bv_type(z3_ctx, width));
  }

  value_cte = expr.get_string("identifier") + expr.type().subtype().get("width").c_str();
  bv = z3_api.mk_var(z3_ctx, value_cte.c_str(), array_type);

  i=0;
  forall_operands(it, expr)
  {
	sprintf(i_str,"%i",i);
	if (int_encoding)
	  int_cte = z3_api.mk_int(z3_ctx, atoi(i_str));
	else
	  int_cte = Z3_mk_int(z3_ctx, atoi(i_str), Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width));

	if (it->type().id()=="array")
	{
	  if (convert_bv(*it, val_cte))
		return true;
	}
	else
	{
	  if (is_signed(it->type()))
	    value_cte = integer2string(binary2integer(it->get("value").c_str(), true),10);
	  else
	    value_cte = integer2string(binary2integer(it->get("value").c_str(), false),10);

	  if (int_encoding)
	  {
		if (it->type().id()=="signedbv")
		  val_cte = Z3_mk_int(z3_ctx, atoi(value_cte.c_str()), Z3_mk_int_type(z3_ctx));
		else if (it->type().id()=="unsignedbv")
		  val_cte = Z3_mk_unsigned_int(z3_ctx, atoi(value_cte.c_str()), Z3_mk_int_type(z3_ctx));
		else if (it->type().id()=="fixedbv")
		  val_cte = Z3_mk_int(z3_ctx, atoi(value_cte.c_str()), Z3_mk_real_type(z3_ctx));
	  }
	  else
	  {
	    val_cte = Z3_mk_int(z3_ctx, atoi(value_cte.c_str()), Z3_mk_bv_type(z3_ctx, width));
	  }
	}

	bv = Z3_mk_store(z3_ctx, bv, int_cte, val_cte);
	++i;
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_constant

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_constant(const exprt &expr, Z3_ast &bv)
{
  std::string value;
  unsigned width;

  if (is_signed(expr.type()))
    value = integer2string(binary2integer(expr.get_string("value"), true),10);
  else
	value = integer2string(binary2integer(expr.get_string("value"), false),10);

  if (expr.type().id()=="unsignedbv")
  {
    if (boolbv_get_width(expr.type(), width))
      return true;

	if (int_encoding)
	  bv = z3_api.mk_unsigned_int(z3_ctx, atoi(value.c_str()));
	else
	  bv = Z3_mk_unsigned_int(z3_ctx, atoi(value.c_str()), Z3_mk_bv_type(z3_ctx, width));
  }
  if (expr.type().id()=="signedbv" || expr.type().id()=="c_enum")
  {
    if (boolbv_get_width(expr.type(), width))
      return true;

	if (int_encoding)
	  bv = z3_api.mk_int(z3_ctx, atoi(value.c_str()));
	else
	  bv = Z3_mk_int(z3_ctx, atoi(value.c_str()), Z3_mk_bv_type(z3_ctx, width));
  }
  else if (expr.type().id()== "fixedbv")
  {
    if (boolbv_get_width(expr.type(), width))
      return true;

	if (int_encoding)
	  bv =  Z3_mk_int(z3_ctx, atoi(value.c_str()), Z3_mk_real_type(z3_ctx));
	else
	  bv = Z3_mk_int(z3_ctx, atoi(value.c_str()), Z3_mk_bv_type(z3_ctx, width));
  }
  else if (expr.type().id()== "pointer")
  {
	if (convert_z3_pointer(expr, value, bv))
	  return true;
  }
  else if (expr.type().id()=="bool")
  {
	if (expr.is_false())
	  bv = Z3_mk_false(z3_ctx);
	else if (expr.is_true())
	  bv = Z3_mk_true(z3_ctx);
  }
  else if (expr.type().id()=="array")
  {
	if (convert_array(expr, bv))
	  return true;
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_bitwise

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_bitwise(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()>=2);
  Z3_ast *args;
  u_int i=0;

  args = new Z3_ast[expr.operands().size()+1];

  if (convert_bv(expr.op0(), args[0]))
    return true;
  if (convert_bv(expr.op1(), args[1]))
	return true;

  forall_operands(it, expr)
  {
    if (convert_bv(*it, args[i]))
      return true;

    if (i>=1)
    {
      if (int_encoding)
        throw "bitwise operations are not supported";
      else
      {
        if(expr.id()=="bitand")
          args[i+1] = Z3_mk_bvand(z3_ctx, args[i-1], args[i]);
        else if(expr.id()=="bitor")
          args[i+1] = Z3_mk_bvor(z3_ctx, args[i-1], args[i]);
    	else if(expr.id()=="bitxor")
    	  args[i+1] = Z3_mk_bvxor(z3_ctx, args[i-1], args[i]);
    	else if (expr.id()=="bitnand")
    	  args[i+1] = Z3_mk_bvnand(z3_ctx, args[i-1], args[i]);
    	else if (expr.id()=="bitnor")
    	  args[i+1] = Z3_mk_bvnor(z3_ctx, args[i-1], args[i]);
    	else if (expr.id()=="bitnxor")
    	  args[i+1] = Z3_mk_bvxnor(z3_ctx, args[i-1], args[i]);
      }
    }
    ++i;
  }

  bv=args[i];

  delete[] args;

 return false;
}

/*******************************************************************
 Function: z3_convt::convert_unary_minus

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_unary_minus(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==1);
  Z3_ast args[2];

  if (convert_bv(expr.op0(), args[0]))
	return true;

  if (int_encoding)
  {
    if (expr.type().id() == "signedbv")
    {
      args[1] = z3_api.mk_int(z3_ctx,-1);
      bv = Z3_mk_mul(z3_ctx, 2, args);
    }
    else if (expr.type().id() == "fixedbv")
    {
      args[1] = Z3_mk_int(z3_ctx, -1, Z3_mk_real_type(z3_ctx));
      bv = Z3_mk_mul(z3_ctx, 2, args);
    }
  }
  else
  {
	bv = Z3_mk_bvneg(z3_ctx, args[0]);
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_if

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_if(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==3);

  Z3_ast operand0, operand1, operand2;

  if (convert_bv(expr.op0(), operand0))
	return true;

  if (convert_bv(expr.op1(), operand1))
	return true;

  if (convert_bv(expr.op2(), operand2))
	return true;

  bv = Z3_mk_ite(z3_ctx, operand0, operand1, operand2);

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_logical_ops

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_logical_ops(const exprt &expr, Z3_ast &bv)
{
  assert(expr.type().id()=="bool");
  Z3_ast args[2];

  if(expr.operands().size()>=2)
  {
	if (convert_bv(expr.op0(), args[0]))
	  return true;
	if (convert_bv(expr.op1(), args[1]))
	  return true;

	if(expr.id()=="and")
	  bv = Z3_mk_and(z3_ctx, 2, args);
	else if(expr.id()=="or")
	  bv = Z3_mk_or(z3_ctx, 2, args);
	else if(expr.id()=="xor")
	  bv = Z3_mk_xor(z3_ctx, args[0], args[1]);
  }
  else if (expr.operands().size()==1)
  {
    if (convert_bv(expr.op0(), bv))
      return true;
  }
  else
    assert(false);

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_logical_not

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_logical_not(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==1);
  Z3_ast operand0;

  if (convert_bv(expr.op0(), operand0))
	return true;

  bv = Z3_mk_not(z3_ctx, operand0);

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_equality

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_equality(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==2);
  assert(expr.op0().type()==expr.op1().type());

  Z3_ast args[2];

  if (convert_bv(expr.op0(), args[0]))
	return true;
  if (convert_bv(expr.op1(), args[1]))
	return true;

  if (expr.id()=="=")
    bv = Z3_mk_eq(z3_ctx, args[0], args[1]);
  else
	bv = Z3_mk_distinct(z3_ctx,2,args);

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_add

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_add(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()>=2);
  Z3_ast *args;
  u_int i=0, size;

  size=expr.operands().size()+1;
  args = new Z3_ast[size];

  if (expr.op0().type().id() == "pointer" || expr.op1().type().id() == "pointer")
  {
    Z3_ast pointer=0;

    forall_operands(it, expr)
    {
      if (convert_bv(*it, args[i]))
        return true;

      if (it->type().id()=="pointer")
      {
    	pointer = args[i];
    	args[i] = z3_api.mk_tuple_select(z3_ctx, pointer, 1); //select pointer index
      }

      if (!int_encoding)
      {
        if (i==1)
        {
          args[size-1]=Z3_mk_bvadd(z3_ctx, args[0], args[1]);
        }
        else if (i>1)
        {
   	      args[size-1] = Z3_mk_bvadd(z3_ctx, args[size-1], args[i]);
        }
      }
      ++i;
    }

  	if (int_encoding)
  	  args[i] = Z3_mk_add(z3_ctx, i, args);

    bv = z3_api.mk_tuple_update(z3_ctx, pointer, 1, args[i]);

    if (expr.type().id() == "signedbv")
      bv=args[i];
  }
  else if (expr.op0().id()=="typecast" || expr.op1().id()=="typecast")
  {
	assert(expr.operands().size()==2);
    if (convert_bv(expr.op0(), args[0]))
      return true;
	if (convert_bv(expr.op1(), args[1]))
	  return true;

	if (expr.op0().id()=="typecast")
	{
	  const exprt &offset=expr.op0().operands()[0];
	  if (offset.type().id()=="pointer")
	    args[0] = z3_api.mk_tuple_select(z3_ctx, args[0], 1); //select pointer index
	}

	if (expr.op1().id()=="typecast")
	{
	  const exprt &offset=expr.op1().operands()[0];
	  if (offset.type().id()=="pointer")
	    args[1] = z3_api.mk_tuple_select(z3_ctx, args[1], 1); //select pointer index
	}

    if (int_encoding)
      bv = Z3_mk_add(z3_ctx, 2, args);
    else
	  bv = Z3_mk_bvadd(z3_ctx, args[0], args[1]);
  }
  else
  {
    forall_operands(it, expr)
    {
      if (convert_bv(*it, args[i]))
        return true;

      if (!int_encoding)
      {
        if (i==1)
        {
          args[size-1]=Z3_mk_bvadd(z3_ctx, args[0], args[1]);
        }
        else if (i>1)
        {
   	      args[size-1] = Z3_mk_bvadd(z3_ctx, args[size-1], args[i]);
        }
      }
      ++i;
    }

  	if (int_encoding)
  	  args[i] = Z3_mk_add(z3_ctx, i, args);

	bv=args[i];
  }

  delete[] args;

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_sub

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_sub(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()>=2);
  Z3_ast *args;
  u_int i=0, size;

  size=expr.operands().size()+1;
  args = new Z3_ast[size];

  if (expr.op0().type().id() == "pointer" || expr.op1().type().id() == "pointer")
  {
    Z3_ast pointer=0;

    forall_operands(it, expr)
    {
      if (convert_bv(*it, args[i]))
        return true;

      if (it->type().id()=="pointer")
      {
    	pointer = args[i];
    	args[i] = z3_api.mk_tuple_select(z3_ctx, pointer, 1); //select pointer index
      }

      if (!int_encoding)
      {
        if (i==1)
        {
          args[size-1]=Z3_mk_bvsub(z3_ctx, args[0], args[1]);
        }
        else if (i>1)
        {
   	      args[size-1] = Z3_mk_bvsub(z3_ctx, args[size-1], args[i]);
        }
      }
      ++i;
    }

  	if (int_encoding)
  	  args[i] = Z3_mk_sub(z3_ctx, i, args);

    bv = z3_api.mk_tuple_update(z3_ctx, pointer, 1, args[i]);

    if (expr.type().id() == "signedbv")
      bv=args[i];
  }
  else if (expr.op0().id()=="typecast" || expr.op1().id()=="typecast")
  {
	assert(expr.operands().size()==2);

    if (convert_bv(expr.op0(), args[0]))
      return true;
	if (convert_bv(expr.op1(), args[1]))
      return true;

	if (expr.op0().id()=="typecast")
	{
	  const exprt &offset=expr.op0().operands()[0];
	  if (offset.type().id()=="pointer")
	    args[0] = z3_api.mk_tuple_select(z3_ctx, args[0], 1); //select pointer index
	}

	if (expr.op1().id()=="typecast")
	{
	  const exprt &offset=expr.op1().operands()[0];
	  if (offset.type().id()=="pointer")
	    args[1] = z3_api.mk_tuple_select(z3_ctx, args[1], 1); //select pointer index
	}

    if (int_encoding)
      bv = Z3_mk_sub(z3_ctx, 2, args);
    else
      bv = Z3_mk_bvsub(z3_ctx, args[0], args[1]);
  }
  else
  {
    forall_operands(it, expr)
    {
      if (convert_bv(*it, args[i]))
        return true;

      if (!int_encoding)
      {
        if (i==1)
        {
          args[size-1]=Z3_mk_bvsub(z3_ctx, args[0], args[1]);
        }
        else if (i>1)
        {
   	      args[size-1] = Z3_mk_bvsub(z3_ctx, args[size-1], args[i]);
        }
      }
      ++i;
    }

  	if (int_encoding)
  	  args[i] = Z3_mk_sub(z3_ctx, i, args);

	bv=args[i];
  }

  delete[] args;

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_div

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_div(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==2);
  Z3_ast operand0, operand1;

  if (convert_bv(expr.op0(), operand0))
	return true;
  if (convert_bv(expr.op1(), operand1))
	return true;

  if (int_encoding)
  {
    bv = Z3_mk_div(z3_ctx, operand0, operand1);
  }
  else
  {
    if (expr.type().id()=="signedbv" || expr.type().id()=="fixedbv")
      bv = Z3_mk_bvsdiv(z3_ctx, operand0, operand1);
    else if (expr.type().id()=="unsignedbv")
	  bv = Z3_mk_bvudiv(z3_ctx, operand0, operand1);
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_mod

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_mod(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==2);
  Z3_ast operand0, operand1;

  if (convert_bv(expr.op0(), operand0))
	return true;
  if (convert_bv(expr.op1(), operand1))
	return true;

  if (int_encoding)
  {
    if(expr.type().id()=="signedbv" || expr.type().id()=="unsignedbv")
	  bv = Z3_mk_mod(z3_ctx, operand0, operand1);
	else if (expr.type().id()=="fixedbv")
	  throw "unsupported type for mod: "+expr.type().id_string();
  }
  else
  {
    if(expr.type().id()=="signedbv")
    {
	  bv = Z3_mk_bvsrem(z3_ctx, operand0, operand1);
    }
	else if (expr.type().id()=="unsignedbv")
	{
	  bv = Z3_mk_bvurem(z3_ctx, operand0, operand1);
	}
	else if (expr.type().id()=="fixedbv")
	  throw "unsupported type for mod: "+expr.type().id_string();
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_mul

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_mul(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()>=2);
  Z3_ast *args;
  u_int i=0, size;

  size=expr.operands().size()+1;
  args = new Z3_ast[size];

  if (expr.op0().type().id() == "pointer" || expr.op1().type().id() == "pointer")
  {
    Z3_ast pointer=0;

    forall_operands(it, expr)
    {
      if (convert_bv(*it, args[i]))
        return true;

      if (it->type().id()=="pointer")
      {
    	pointer = args[i];
    	args[i] = z3_api.mk_tuple_select(z3_ctx, pointer, 1); //select pointer index
      }

      if (!int_encoding)
      {
        if (i==1)
        {
          args[size-1]=Z3_mk_bvmul(z3_ctx, args[0], args[1]);
        }
        else if (i>1)
        {
   	      args[size-1] = Z3_mk_bvmul(z3_ctx, args[size-1], args[i]);
        }
      }
      ++i;
    }

  	if (int_encoding)
  	  args[i] = Z3_mk_mul(z3_ctx, i, args);

    bv = z3_api.mk_tuple_update(z3_ctx, pointer, 1, args[i]);
  }
  else if (expr.op0().id()=="typecast" || expr.op1().id()=="typecast")
  {
	assert(expr.operands().size()==2);

    if (convert_bv(expr.op0(), args[0]))
      return true;
    if (convert_bv(expr.op1(), args[1]))
      return true;

	if (expr.op0().id()=="typecast")
	{
	  const exprt &offset=expr.op0().operands()[0];
	  if (offset.type().id()=="pointer")
	    args[0] = z3_api.mk_tuple_select(z3_ctx, args[0], 1); //select pointer index
	}

	if (expr.op1().id()=="typecast")
	{
	  const exprt &offset=expr.op1().operands()[0];
	  if (offset.type().id()=="pointer")
	    args[1] = z3_api.mk_tuple_select(z3_ctx, args[1], 1); //select pointer index
	}

    if (int_encoding)
      bv = Z3_mk_mul(z3_ctx, 2, args);
    else
	  bv = Z3_mk_bvmul(z3_ctx, args[0], args[1]);
  }
  else
  {
    forall_operands(it, expr)
    {
      if (convert_bv(*it, args[i]))
        return true;

      if (!int_encoding)
      {
        if (i==1)
        {
          args[size-1]=Z3_mk_bvmul(z3_ctx, args[0], args[1]);
        }
        else if (i>1)
        {
   	      args[size-1] = Z3_mk_bvmul(z3_ctx, args[size-1], args[i]);
        }
      }
      ++i;
    }

  	if (int_encoding)
  	  args[i] = Z3_mk_mul(z3_ctx, i, args);

	bv=args[i];
  }

  delete[] args;

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_pointer

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_pointer(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==1);
  assert(expr.type().id()=="pointer");

  static Z3_ast pointer_var, pointer;
  Z3_type_ast pointer_type;
  Z3_ast offset, po, pi;
  std::string symbol_name, out;

  if (create_pointer_type(expr.type(), pointer_type))
	return true;

  offset = convert_number(0, config.ansi_c.int_width, true);

  if (expr.op0().id() == "index")
  {
    const exprt &object=expr.op0().operands()[0];
	const exprt &index=expr.op0().operands()[1];

    symbol_name = "address_of_index" + object.id_string() + object.get_string("identifier");
	pointer_var = z3_api.mk_var(z3_ctx, symbol_name.c_str(), pointer_type);

	if (object.id()=="zero_string")
	{
	  if (convert_zero_string(object, po))
	    return true;
	}
	else if (object.id()==ID_string_constant)
	{
	  if (convert_bv(object, po))
		return true;
	}
	else if (object.type().id() == "array" && object.type().subtype().id() != "struct")
	{
	  if (read_cache(object, po))
		return true;
	}
	else
	{
	  if (convert_bv(object, po))
		return true;
	}

	if (convert_bv(index, pi))
	  return true;

	if (select_pointer_value(po, pi, pointer))
	  return true;

	if (expr.op0().type().id()!="struct")
	{
      pointer_var = z3_api.mk_tuple_update(z3_ctx, pointer_var, 0, pointer); //update object
      bv = z3_api.mk_tuple_update(z3_ctx, pointer_var, 1, pi); //update offset
      return false;
	}
  }
  else if (expr.op0().id() == "symbol")
  {
	if (expr.op0().type().id() == "signedbv" || expr.op0().type().id() == "fixedbv"
		|| expr.op0().type().id() == "unsignedbv")
	{
	  if (convert_z3_pointer(expr, expr.op0().get_string("identifier"), pointer_var))
		return true;
	}
	else if (expr.op0().type().id() == "pointer")
	{
	  if (convert_bv(expr.op0(), pointer_var))
		return true;
	}
	else if (expr.op0().type().id() == "struct")
	{
	  if (expr.type().subtype().id()=="symbol")
		  return true;

	  symbol_name = "address_of_struct" + expr.op0().get_string("identifier");
	  pointer_var = z3_api.mk_var(z3_ctx, symbol_name.c_str(), pointer_type);

	  if (convert_bv(expr.op0(), pointer))
		return true;

	  pointer_var = z3_api.mk_tuple_update(z3_ctx, pointer_var, 0, pointer); //update object

    }
  }
  else if (expr.op0().id() == "member")
  {
	const exprt &object=expr.op0().operands()[0];

    symbol_name = "address_of_member" + object.get_string("identifier");
	pointer_var = z3_api.mk_var(z3_ctx, symbol_name.c_str(), pointer_type);

	if (convert_bv(expr.op0(), pointer))
	  return true;

	pointer_var = z3_api.mk_tuple_update(z3_ctx, pointer_var, 0, pointer); //update object
  }

  bv = z3_api.mk_tuple_update(z3_ctx, pointer_var, 1, offset); //update offset

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_array_of

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_array_of(const exprt &expr, Z3_ast &bv)
{
  Z3_ast value, index;
  Z3_type_ast array_type=0;
  const array_typet &array_type_size=to_array_type(expr.type());
  std::string tmp, out, identifier;
  static u_int size, j, inc=0;
  unsigned width;

  tmp = integer2string(binary2integer(array_type_size.size().get_string("value"), false),10);
  size = atoi(tmp.c_str());
  size = (size==0) ? 1 : size; //fill in at least one position
  index = convert_number(j, config.ansi_c.int_width, true);

  if (convert_bv(expr.op0(), value))
	return true;

  if (create_array_type(expr.type(), array_type))
	return true;

  if (boolbv_get_width(expr.op0().type(), width))
    return true;

  if (expr.type().subtype().id()=="bool")
  {
    value = Z3_mk_false(z3_ctx);
    identifier = "ARRAY_OF(false)" + width;
    bv = z3_api.mk_var(z3_ctx, identifier.c_str(), array_type);
  }
  else if (expr.type().subtype().id()=="signedbv" || expr.type().subtype().id()=="unsignedbv")
  {
	++inc;
	identifier = "ARRAY_OF(0)" + width + inc;
    bv = z3_api.mk_var(z3_ctx, identifier.c_str(), array_type);
  }
  else if (expr.type().subtype().id()=="fixedbv")
  {
	identifier = "ARRAY_OF(0l)" + width;
	bv = z3_api.mk_var(z3_ctx, identifier.c_str(), array_type);
  }
  else if (expr.type().subtype().id()=="pointer")
  {
	identifier = "ARRAY_OF(0p)" + width;
	bv = z3_api.mk_var(z3_ctx, identifier.c_str(), array_type);
	value = z3_api.mk_tuple_select(z3_ctx, value, 0); //select pointer object
  }
  else if (expr.type().id()=="array" && expr.type().subtype().id()=="struct")
  {
	std::string identifier;
	identifier = "array_of_" + expr.op0().type().get_string("tag");
    bv = z3_api.mk_var(z3_ctx, identifier.c_str(), array_type);
  }
  else if (expr.type().subtype().id()=="array")
  {
	++inc;
	identifier = "ARRAY_OF(0a)" + width + inc;
	out = "identifier: "+ identifier;
	bv = z3_api.mk_var(z3_ctx, identifier.c_str(), array_type);
  }

  //update array
  for (j=0; j<size; j++)
  {
    index = convert_number(j, config.ansi_c.int_width, true);
    bv = Z3_mk_store(z3_ctx, bv, index, value);
    out = "j: "+ j;
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_index

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_index(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==2);

  Z3_ast args[2], pointer;
  std::string identifier;

  if (convert_bv(expr.op0(), args[0]))
	return true;
  if (convert_bv(expr.op1(), args[1]))
	return true;

  if (expr.op0().type().subtype().id() == "pointer")
  {
	bv = Z3_mk_select(z3_ctx, args[0], args[1]);

    if (convert_z3_pointer(expr.op0(), "index", pointer))
      return true;

    bv = z3_api.mk_tuple_update(z3_ctx, pointer, 0, bv);
  }
  else
  {
	bv = Z3_mk_select(z3_ctx, args[0], args[1]);
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_shift

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_shift(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==2);
  Z3_ast operand0, operand1;
  unsigned width_expr, width_op0, width_op1;

  if (convert_bv(expr.op0(), operand0))
	return true;
  if (convert_bv(expr.op1(), operand1))
	return true;

  if(boolbv_get_width(expr.type(), width_expr))
	  return true;

  if(boolbv_get_width(expr.op0().type(), width_op0))
	  return true;

  if(boolbv_get_width(expr.op1().type(), width_op1))
	  return true;

  if (width_op0>width_expr)
    operand0 = Z3_mk_extract(z3_ctx, (width_expr-1), 0, operand0);
  if (width_op1>width_expr)
    operand1 = Z3_mk_extract(z3_ctx, (width_expr-1), 0, operand1);

  if (int_encoding)
	throw "bitshift operations are not supported yet";
  else
  {
    if(expr.id()=="ashr")
      bv = Z3_mk_bvashr(z3_ctx, operand0, operand1);
    else if (expr.id()=="lshr")
      bv = Z3_mk_bvlshr(z3_ctx, operand0, operand1);
    else if(expr.id()=="shl")
      bv = Z3_mk_bvshl(z3_ctx, operand0, operand1);
    else
      assert(false);
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_abs

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_abs(const exprt &expr, Z3_ast &bv)
{
  unsigned width;
  std::string out;

  if (boolbv_get_width(expr.type(), width))
    return true;

  const exprt::operandst &operands=expr.operands();

  if(operands.size()!=1)
    throw "abs takes one operand";

  const exprt &op0=expr.op0();
  static Z3_ast zero, one, is_negative, val_orig, val_mul;

  out = "width: "+ width;
  if (expr.type().id()=="signedbv" || expr.type().id()=="fixedbv")
    zero = convert_number(0, width, true);
  else if (expr.type().id()=="unsignedbv")
	zero = convert_number(0, width, false);

  one = convert_number(-1, width, true);

  if (convert_bv(op0, val_orig))
	return true;

  if (expr.type().id()=="signedbv" || expr.type().id()=="fixedbv")
    is_negative = Z3_mk_bvslt(z3_ctx, val_orig, zero);

  val_mul = Z3_mk_bvmul(z3_ctx, val_orig, one);
  bv = Z3_mk_ite(z3_ctx, is_negative, val_mul, val_orig);

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_with

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_with(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()>=1);
  Z3_ast array_var, array_val, operand0, operand1, operand2;

  if (expr.type().id() == "struct" || expr.type().id() == "union")
  {
	if (convert_bv(expr.op0(), array_var))
	  return true;

	if (convert_bv(expr.op2(), array_val))
	  return true;

	bv = z3_api.mk_tuple_update(z3_ctx, array_var,
			convert_member_name(expr.op0(), expr.op1()), array_val);
  }
  else
  {
    if (convert_bv(expr.op0(), operand0))
      return true;
    if (convert_bv(expr.op1(), operand1))
      return true;
    if (convert_bv(expr.op2(), operand2))
      return true;

	if (expr.op2().type().id() == "pointer")
	{
      if (select_pointer_value(operand0, operand1, operand2)) //select pointer value
    	return true;
	}
	else if (expr.op2().id() == "typecast")
	{
	  if (select_pointer_value(operand0, operand1, operand2)) //select pointer value
	    return true;
	}

	bv = Z3_mk_store(z3_ctx, operand0, operand1, operand2);
  }

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_bitnot

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_bitnot(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==1);
  Z3_ast operand0;

  if (convert_bv(expr.op0(), operand0))
	return true;

  if (int_encoding)
    bv = Z3_mk_not(z3_ctx, operand0);
  else
	bv = Z3_mk_bvnot(z3_ctx, operand0);

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_member_name

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

u_int z3_convt::convert_member_name(const exprt &lhs, const exprt &rhs)
{
  const struct_typet &struct_type=to_struct_type(lhs.type());
  const struct_typet::componentst &components=struct_type.components();
  u_int i=0, resp=0;

  for(struct_typet::componentst::const_iterator
    it=components.begin();
    it!=components.end();
    it++, i++)
  {
	if (it->get("name").compare(rhs.get_string("component_name")) == 0)
      resp=i;
  }

  return resp;
}

/*******************************************************************
 Function: z3_convt::convert_object

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_object(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==2);
  Z3_ast args[2];

  if (convert_bv(expr.op0(), args[0]))
	return true;
  if (convert_bv(expr.op1(), args[1]))
	return true;

  args[0] = z3_api.mk_tuple_select(z3_ctx, args[0], 0);
  args[1] = z3_api.mk_tuple_select(z3_ctx, args[1], 0);

  bv = Z3_mk_distinct(z3_ctx, 2, args);

  return false;
}

/*******************************************************************
 Function: z3_convt::select_pointer_offset

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::select_pointer_offset(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==1);
  static Z3_ast pointer;

  if (convert_bv(expr.op0(), pointer))
	return true;

  bv = z3_api.mk_tuple_select(z3_ctx, pointer, 1); //select pointer offset

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_member

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_member(const exprt &expr, Z3_ast &bv)
{
  const struct_typet &struct_type=to_struct_type(expr.op0().type());
  const struct_typet::componentst &components=struct_type.components();
  u_int i=0, j=0;
  Z3_ast struct_var;

  if (convert_bv(expr.op0(), struct_var))
	return true;

  for(struct_typet::componentst::const_iterator
    it=components.begin();
    it!=components.end();
    it++, i++)
  {
	if (it->get("name").compare(expr.get_string("component_name")) == 0)
	  j=i;
  }

  bv = z3_api.mk_tuple_select(z3_ctx, struct_var, j);

  return false;
}

/*******************************************************************
 Function: convert_pointer_object

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_pointer_object(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==1 && is_ptr(expr.op0().type()));
  Z3_ast pointer_object=0;
  const exprt &object=expr.op0().operands()[0];
  unsigned width, object_width;

  if (boolbv_get_width(expr.type(), width))
	  return true;


  if (expr.op0().id()=="symbol" || expr.op0().id()=="constant")
  {
    if (convert_bv(expr.op0(), pointer_object))
      return true;
    pointer_object = z3_api.mk_tuple_select(z3_ctx, pointer_object, 0);

    if (expr.op0().type().id()=="pointer")
    {
      if (expr.op0().type().subtype().id()=="empty" || expr.op0().type().subtype().id()=="symbol")
      {
        object_width = config.ansi_c.int_width;
      }
      else
      {
    	if (boolbv_get_width(expr.op0().type().subtype(), object_width))
   		  return true;
      }
    }
    else
    {
   	  if (boolbv_get_width(expr.op0().type(), object_width))
  		return true;
    }

    if (width>object_width)
      return Z3_mk_zero_ext(z3_ctx, (width-object_width), pointer_object);
    else if (width<object_width)
  	  return Z3_mk_extract(z3_ctx, (width-1), 0, pointer_object);
    else if (width==object_width)
      return pointer_object;
  }
  else if (object.id()=="index" && object.type().id() == "struct")
  {
	const exprt &symbol=object.operands()[0];
	const exprt &index=object.operands()[1];
	Z3_ast array_value, array, array_index;

	if (convert_bv(symbol, array))
	  return true;

	if (convert_bv(index, array_index))
	  return true;

	array_value = Z3_mk_select(z3_ctx, array, array_index);
	pointer_object = z3_api.mk_tuple_select(z3_ctx, array_value, 0);

	const struct_typet &struct_type=to_struct_type(object.type());
    const struct_typet::componentst &components=struct_type.components();
    u_int i=0;
    char val[2];

    for(struct_typet::componentst::const_iterator
      it=components.begin();
      it!=components.end();
      it++, i++)
    {
	  if (it->type().id() == "pointer")
	  {
		sprintf(val,"%i",i);
	    if (int_encoding)
	      pointer_object = z3_api.mk_int(z3_ctx, atoi(val));
		else
		  pointer_object = Z3_mk_int(z3_ctx, atoi(val), Z3_mk_bv_type(z3_ctx, config.ansi_c.int_width));
	  }
    }
  }
  else
  {
    if (convert_bv(object, pointer_object))
      return true;

    if (object.type().id()=="signedbv" || object.type().id()=="unsignedbv"
    	|| object.type().id()=="fixedbv")
    {
   	  if (boolbv_get_width(object.type(), object_width))
   		return true;

      if (width>object_width)
        return Z3_mk_zero_ext(z3_ctx, (width-object_width), pointer_object);
      else if (width<object_width)
    	return Z3_mk_extract(z3_ctx, (width-1), 0, pointer_object);
    }
    else if (object.type().id()=="array")
    {
      Z3_ast args[2];
      const exprt &object_array=expr.op0().operands()[0];
      const exprt &object_index=expr.op0().operands()[1];

      if (convert_bv(object_array, args[0]))
    	return true;
      if (convert_bv(object_index, args[1]))
    	return true;

      pointer_object = Z3_mk_select(z3_ctx, args[0], args[1]);

      if (object_array.type().subtype().id()=="pointer")
      {
        if (boolbv_get_width(object_array.type().subtype().subtype(), object_width))
       	  return true;
      }
      else
      {
        if (boolbv_get_width(object_array.type().subtype(), object_width))
       	  return true;
      }

      if (width>object_width)
        return Z3_mk_zero_ext(z3_ctx, (width-object_width), pointer_object);
      else if (width<object_width)
    	  return Z3_mk_extract(z3_ctx, (width-1), 0, pointer_object);
      else if (width==object_width)
        return pointer_object;

    }
    else if (object.type().id()=="pointer")
    {
      Z3_ast args[2];
      const exprt &object_array=object.operands()[0];

      if (object_array.type().id()=="array")
      {
        const exprt &object_index=object.operands()[1];

        if (convert_bv(object_array, args[0]))
          return true;
        if (convert_bv(object_index, args[1]))
          return true;

        pointer_object = Z3_mk_select(z3_ctx, args[0], args[1]);

        if (expr.op0().type().subtype().id()=="empty")
        {
          object_width = config.ansi_c.int_width;
        }
       else
       {
         if (boolbv_get_width(object.type().subtype(), object_width))
           return true;
       }

        if (width>object_width)
          return Z3_mk_zero_ext(z3_ctx, (width-object_width), pointer_object);
        else if (width<object_width)
    	  return Z3_mk_extract(z3_ctx, (width-1), 0, pointer_object);
        else if (width==object_width)
          return pointer_object;
      }
    }
    else if (object.type().id()=="struct")
    {
   	  const struct_typet &struct_type=to_struct_type(object.type());
      const struct_typet::componentst &components=struct_type.components();

      pointer_object = z3_api.mk_tuple_select(z3_ctx, pointer_object, 0);

	  for(struct_typet::componentst::const_iterator
	    it=components.begin();
	    it!=components.end();
	    it++)
	  {
	    if (it->type().id() == expr.type().id())
	    {
          if (boolbv_get_width(it->type(), object_width))
            return true;

	      if (width==object_width)
	      {
	    	if (convert_identifier(it->get("name").c_str(), it->type(), bv))
	    	  return true;

	    	return false;
	      }
	    }
	    else
	    {
          if (boolbv_get_width(it->type(), object_width))
            return true;

		   if (width==object_width)
		   {
			  if (convert_identifier(it->get("name").c_str(), expr.type(), bv/*pointer_object*/))
				 return true;

			  return false;
		   }
	    }
	  }
  	  bv = Z3_mk_zero_ext(z3_ctx, (width-object_width), pointer_object);
  	  return false;
    }
  }

  bv = pointer_object;

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_zero_string_length

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_zero_string_length(const exprt &expr, Z3_ast &bv)
{
  assert(expr.operands().size()==1);
  Z3_ast operand;

  if (convert_bv(expr.op0(), operand))
	return true;

  bv = z3_api.mk_tuple_select(z3_ctx, operand, 0);

  return false;
}

/*******************************************************************
 Function: z3_convt::convert_z3_expr

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::convert_z3_expr(const exprt &expr, Z3_ast &bv)
{
  if (expr.id() == "symbol")
	return convert_identifier(expr.get_string("identifier"), expr.type(), bv);
  else if (expr.id() == "nondet_symbol")
	return convert_identifier("nondet$"+expr.get_string("identifier"), expr.type(), bv);
  else if (expr.id() == "typecast")
    return convert_typecast(expr, bv);
  else if (expr.id() == "struct" || expr.id() == "union")
	return convert_struct(expr, bv);
  else if (expr.id() == "constant")
	return convert_constant(expr, bv);
  else if (expr.id() == "bitand" || expr.id() == "bitor" || expr.id() == "bitxor"
		|| expr.id() == "bitnand" || expr.id() == "bitnor" || expr.id() == "bitnxor")
    return convert_bitwise(expr, bv);
  else if (expr.id() == "bitnot")
	return convert_bitnot(expr, bv);
  else if (expr.id() == "unary-")
    return convert_unary_minus(expr, bv);
  else if (expr.id() == "if")
    return convert_if(expr, bv);
  else if (expr.id() == "and" || expr.id() == "or" || expr.id() == "xor")
	return convert_logical_ops(expr, bv);
  else if (expr.id() == "not")
	return convert_logical_not(expr, bv);
  else if (expr.id() == "=" || expr.id() == "notequal")
	return convert_equality(expr, bv);
  else if (expr.id() == "<=" || expr.id() == "<" || expr.id() == ">="
		|| expr.id() == ">")
	return convert_rel(expr, bv);
  else if (expr.id() == "+")
	return convert_add(expr, bv);
  else if (expr.id() == "-")
	return convert_sub(expr, bv);
  else if (expr.id() == "/")
	return convert_div(expr, bv);
  else if (expr.id() == "mod")
	return convert_mod(expr, bv);
  else if (expr.id() == "*")
	return convert_mul(expr, bv);
  else if (expr.id() == "address_of" || expr.id() == "implicit_address_of"
		|| expr.id() == "reference_to")
	return convert_pointer(expr, bv);
  else if (expr.id() == "array_of")
	return convert_array_of(expr, bv);
  else if (expr.id() == "index")
	return convert_index(expr, bv);
  else if (expr.id() == "ashr" || expr.id() == "lshr" || expr.id() == "shl")
	return convert_shift(expr, bv);
  else if(expr.id()=="abs")
    return convert_abs(expr, bv);
  else if (expr.id() == "with")
	return convert_with(expr, bv);
  else if (expr.id() == "member")
	return convert_member(expr, bv);
  else if (expr.id()=="zero_string")
	return convert_zero_string(expr, bv);
  else if (expr.id() == "pointer_offset")
	return select_pointer_offset(expr, bv);
  else if (expr.id() == "pointer_object")
	return convert_pointer_object(expr, bv);
  else if (expr.id() == "same-object")
	return convert_object(expr, bv);
  else if (expr.id() == ID_string_constant) {
	  exprt tmp;
	  string2array(expr, tmp);
	return convert_bv(tmp, bv);
  } else if (expr.id() == "zero_string_length")
    return convert_zero_string_length(expr.op0(), bv);
  else if (expr.id() == "replication")
	assert(expr.operands().size()==2);
#if 0
  else if(expr.id()=="isnan") {
	ignoring(expr);
	return convert_bv(expr.op0());
  }
#endif

  return true;
}

/*******************************************************************
 Function: z3_convt::assign_z3_expr

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

bool z3_convt::assign_z3_expr(const exprt expr)
{
  u_int size = expr.operands().size();

  //ignore these IRep expressions for now. I don't know what they mean.

  if ((expr.op0().id()=="index" && expr.op0().type().id() == "pointer"
  	       && expr.op0().type().subtype().id()=="symbol")
  	       && (expr.id()=="invalid-pointer" || expr.id()=="same-object" || expr.id()=="is_dynamic_object"))
  {
  	ignoring(expr);
  	ignoring_expr=false;
  	return false;
  }
  else if (expr.op0().id()=="symbol" && expr.op0().type().id() == "array"
	  && expr.op0().type().subtype().id()=="pointer"
	  && expr.op0().type().subtype().subtype().id()=="symbol"
	  && expr.id()!="is_dynamic_object" && expr.id()!="invalid-pointer")
  {
	  if (expr.op1().id()=="array_of" && expr.op1().type().id() == "array"
	  	  && expr.op1().type().subtype().id()=="pointer"
	  	  && expr.op1().type().subtype().subtype().id()=="symbol")
	  {
	    ignoring(expr);
	    ignoring_expr=false;
	    return false;
	  }
  }
  else if (size==2 && expr.op1().id() == "unary+")
  {
    ignoring(expr.op1());
    ignoring_expr=false;
	return false;
  }

  return true;
}

/*******************************************************************
 Function: z3_convt::set_to

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

void z3_convt::set_to(const exprt &expr, bool value)
{
#ifdef DEBUG
  std::cout << "\n" << __FUNCTION__ << "[" << __LINE__ << "]" << "\n";
#endif

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

  if(boolean)
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

	Z3_ast result, operand[2];
    const exprt &op0=expr.op0();
	const exprt &op1=expr.op1();

	if (assign_z3_expr(expr) && ignoring_expr)
	{
	  if (convert_bv(op0, operand[0]))
		return;
	  if (convert_bv(op1, operand[1]))
		return ;

	  if (op0.type().id()=="pointer" && op1.type().id()=="pointer")
	  {
	    static Z3_ast pointer[2], formula[2];

		pointer[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 0); //select object
		pointer[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 0);
		formula[0] = Z3_mk_eq(z3_ctx, pointer[0], pointer[1]);

		pointer[0] = z3_api.mk_tuple_select(z3_ctx, operand[0], 1); //select index
		pointer[1] = z3_api.mk_tuple_select(z3_ctx, operand[1], 1);
		formula[1] = Z3_mk_eq(z3_ctx, pointer[0], pointer[1]);

		result = Z3_mk_and(z3_ctx, 2, formula);
		Z3_assert_cnstr(z3_ctx, result);
	  }
	  else
	  {
	    result = Z3_mk_eq(z3_ctx, operand[0], operand[1]);
	    Z3_assert_cnstr(z3_ctx, result);
	  }
	}
  }
  ignoring_expr=true;
}

/*******************************************************************
 Function: z3_convt::get_number_vcs_z3

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

u_int z3_convt::get_number_vcs_z3(void)
{
  return number_vcs_z3;
}

/*******************************************************************
 Function: z3_convt::get_number_variables_z

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/

u_int z3_convt::get_number_variables_z3(void)
{
  return number_variables_z3;
}
