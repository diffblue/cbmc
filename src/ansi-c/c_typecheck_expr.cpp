/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <arith_tools.h>
#include <bitvector.h>
#include <config.h>
#include <expr_util.h>
#include <std_types.h>
#include <prefix.h>
#include <cprover_prefix.h>
#include <simplify_expr.h>
#include <base_type.h>
#include <std_expr.h>
#include <i2string.h>

#include "c_types.h"
#include "c_typecast.h"
#include "c_typecheck_base.h"
#include "c_sizeof.h"
#include "c_qualifiers.h"
#include "string_constant.h"
#include "anonymous_member.h"
#include "padding.h"

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr(exprt &expr)
{
  if(expr.id()=="already_typechecked")
  {
    assert(expr.operands().size()==1);
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
    return;
  }

  // fist do sub-nodes
  typecheck_expr_operands(expr);

  // now do case-split
  typecheck_expr_main(expr);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool c_typecheck_baset::gcc_types_compatible_p(const typet &type1, const typet &type2)
{
  // read
  // http://gcc.gnu.org/onlinedocs/gcc-3.3.6/gcc/Other-Builtins.html
  
  if(type1.id()==ID_symbol)
    return gcc_types_compatible_p(follow(type1), type2);
  else if(type2.id()==ID_symbol)
    return gcc_types_compatible_p(type1, follow(type2));

  // check qualifiers first
  if(c_qualifierst(type1)!=c_qualifierst(type2))
    return false;

  if(type1.id()==ID_c_enum)
  {
    if(type2==int_type())
      return true;
    else if(type2==type1) // compares the tag
      return true;
  }
  else if(type2.id()==ID_c_enum)
  {
    if(type1==int_type())
      return true;
    else if(type1==type2) // compares the tag
      return true;
  }
  else if(type1.id()==ID_pointer && type2.id()==ID_pointer)
    return gcc_types_compatible_p(type1.subtype(), type2.subtype());
  else if(type1.id()==ID_array && type2.id()==ID_array)
    return gcc_types_compatible_p(type1.subtype(), type2.subtype()); // ignore size
  else if(type1==type2)
    return true;
  
  return false;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_main(exprt &expr)
{
  if(expr.id()==ID_sideeffect)
    typecheck_expr_side_effect(to_side_effect_expr(expr));
  else if(expr.id()==ID_constant)
    typecheck_expr_constant(expr);
  else if(expr.id()==ID_infinity)
  {
    // ignore
  }
  else if(expr.id()==ID_symbol)
    typecheck_expr_symbol(expr);
  else if(expr.id()==ID_unary_plus ||
          expr.id()==ID_unary_minus ||
          expr.id()==ID_bitnot)
    typecheck_expr_unary_arithmetic(expr);
  else if(expr.id()==ID_not)
    typecheck_expr_unary_boolean(expr);
  else if(expr.id()==ID_and || expr.id()==ID_or || expr.id()==ID_implies)
    typecheck_expr_binary_boolean(expr);
  else if(expr.id()==ID_address_of)
    typecheck_expr_address_of(expr);
  else if(expr.id()==ID_dereference)
    typecheck_expr_dereference(expr);
  else if(expr.id()==ID_member)
    typecheck_expr_member(expr);
  else if(expr.id()==ID_ptrmember)
    typecheck_expr_ptrmember(expr);
  else if(expr.id()==ID_equal  ||
          expr.id()==ID_notequal ||
          expr.id()==ID_lt  ||
          expr.id()==ID_le ||
          expr.id()==ID_gt  ||
          expr.id()==ID_ge)
    typecheck_expr_rel(expr);
  else if(expr.id()==ID_index)
    typecheck_expr_index(expr);
  else if(expr.id()==ID_typecast)
    typecheck_expr_typecast(expr);
  else if(expr.id()==ID_sizeof)
    typecheck_expr_sizeof(expr);
  else if(expr.id()==ID_alignof)
    typecheck_expr_alignof(expr);
  else if(expr.id()==ID_plus || expr.id()==ID_minus ||
          expr.id()==ID_mult || expr.id()==ID_div ||
          expr.id()==ID_mod ||
          expr.id()==ID_bitand || expr.id()==ID_bitxor || expr.id()==ID_bitor)
    typecheck_expr_binary_arithmetic(expr);
  else if(expr.id()==ID_shl || expr.id()==ID_shr)
    typecheck_expr_shifts(to_shift_expr(expr));
  else if(expr.id()==ID_comma)
    typecheck_expr_comma(expr);
  else if(expr.id()==ID_if)
    typecheck_expr_trinary(to_if_expr(expr));
  else if(expr.id()==ID_code)
  {
    err_location(expr);
    str << "typecheck_expr_main got code: " << expr.pretty();
    throw 0;
  }
  else if(expr.id()==ID_gcc_builtin_va_arg)
    typecheck_expr_builtin_va_arg(expr);
  else if(expr.id()==ID_cw_va_arg_typeof)
    typecheck_expr_cw_va_arg_typeof(expr);
  else if(expr.id()==ID_gcc_builtin_types_compatible_p)
  {
    expr.type()=bool_typet();
    typet::subtypest &subtypes=((typet &)(expr)).subtypes();
    assert(subtypes.size()==2);
    typecheck_type(subtypes[0]);
    typecheck_type(subtypes[1]);
    locationt location=expr.location();
    
    // ignores top level qualifiers
    subtypes[0].remove(ID_C_constant);
    subtypes[0].remove(ID_C_volatile);
    subtypes[0].remove(ID_C_restricted);
    subtypes[1].remove(ID_C_constant);
    subtypes[1].remove(ID_C_volatile);
    subtypes[1].remove(ID_C_restricted);
    
    expr.make_bool(gcc_types_compatible_p(subtypes[0], subtypes[1]));
    expr.location()=location;
  }
  else if(expr.id()==ID_builtin_offsetof)
    typecheck_expr_builtin_offsetof(expr);
  else if(expr.id()==ID_string_constant)
  {
    // already fine -- mark as lvalue
    expr.set(ID_C_lvalue, true);
  }
  else if(expr.id()==ID_arguments)
  {
    // already fine
  }
  else if(expr.id()==ID_designated_initializer)
  {
    exprt &designator=static_cast<exprt &>(expr.add(ID_designator));

    Forall_operands(it, designator)
    {
      if(it->id()==ID_index)
      {
        assert(it->operands().size()==1);
        typecheck_expr(it->op0()); // still needs typechecking
      }
    }
  }
  else if(expr.id()==ID_initializer_list)
  {
    // already fine, just set some type
    expr.type()=empty_typet();
  }
  else if(expr.id()==ID_forall ||
          expr.id()==ID_exists)
  {
    // op0 is a declaration,
    // op1 the bound expression
    assert(expr.operands().size()==2);
    expr.type()=bool_typet();
    
    if(expr.op0().operands().size()!=1 ||
       expr.op0().op0().get(ID_statement)!=ID_decl)
    {
      err_location(expr);
      throw "expected declaration as operand of quantifier";
    }

    // replace declaration by symbol expression
    symbol_exprt bound=to_symbol_expr(expr.op0().op0().op0());
    expr.op0().swap(bound);
  }
  else if(expr.id()==ID_label)
  {
    expr.type()=empty_typet();
  }
  else if(expr.id()==ID_array)
  {
    // these pop up as string constants, and are already typed
  }
  else if(expr.id()==ID_complex)
  {
    // these should only exist as constants,
    // and should already be typed
  }
  else if(expr.id()==ID_complex_real ||
          expr.id()==ID_complex_imag)
  {
    // get the subtype
    assert(expr.operands().size()==1);
    const typet &op_type=follow(expr.op0().type());
    if(op_type.id()!=ID_complex)
    {
      err_location(expr);
      throw "expected complex-typed operand";
    }

    expr.type()=op_type.subtype();
    
    // these are lvalues if the operand is one
    if(expr.op0().get_bool(ID_C_lvalue))
      expr.set(ID_C_lvalue, true);
      
    if(expr.op0().get_bool(ID_C_constant))
      expr.set(ID_C_constant, true);
  }
  else if(expr.id()==ID_generic_selection)
  {
    // This is C11.
    // The operand is already typechecked. Depending
    // on it's type, we return one of the generic associatios.
    
    if(expr.operands().size()!=1)
    {
      err_location(expr);
      throw "_Generic expects one operand";
    }

    // This is one of the few places where it's detectable
    // that we are using "bool" for boolean operators instead
    // of "int". We convert for this reason.
    if(follow(expr.op0().type()).id()==ID_bool)
      expr.op0().make_typecast(int_type());

    irept::subt &generic_associations=
      expr.add(ID_generic_associations).get_sub();
      
    // first typecheck all types
    Forall_irep(it, generic_associations)
      if(it->get(ID_type_arg)!=ID_default)
      {
        typet &type=static_cast<typet &>(it->add(ID_type_arg));
        typecheck_type(type);
      }

    // first try non-default match
    exprt default_match=nil_exprt();
    exprt assoc_match=nil_exprt();
    
    const typet &op_type=follow(expr.op0().type());
    
    forall_irep(it, generic_associations)
    {
      if(it->get(ID_type_arg)==ID_default)
        default_match=static_cast<const exprt &>(it->find(ID_value));
      else if(op_type==follow(static_cast<const typet &>(it->find(ID_type_arg))))
        assoc_match=static_cast<const exprt &>(it->find(ID_value));
    }
    
    if(assoc_match.is_nil())
    {
      if(default_match.is_not_nil())
        expr.swap(default_match);
      else
      {
        err_location(expr);
        str << "unmatched generic selection: "
            << to_string(expr.op0().type());
        throw 0;
      }
    }
    else
      expr.swap(assoc_match);

    // still need to typecheck the result
    typecheck_expr(expr);
  }
  else
  {
    err_location(expr);
    str << "unexpected expression: " << expr.pretty();
    throw 0;
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_comma

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_comma(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "comma operator expects two operands";
    throw 0;
  }

  expr.type()=expr.op1().type();

  // make this an l-value if the last operand is one
  if(expr.op1().get_bool(ID_C_lvalue))
    expr.set(ID_C_lvalue, true);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_builtin_va_arg

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_builtin_va_arg(exprt &expr)
{
  // this comes with a type, which will need to be fixed
  // and checked
  typet type=expr.type();
  typecheck_type(type);
  
  code_typet new_type;
  new_type.return_type().swap(type);
  new_type.arguments().resize(1);
  new_type.arguments()[0].type()=pointer_typet(empty_typet());

  assert(expr.operands().size()==1);  
  exprt arg=expr.op0();

  implicit_typecast(arg, pointer_typet(empty_typet()));

  // turn into function call
  side_effect_expr_function_callt result;
  result.location()=expr.location();
  result.function()=symbol_exprt(ID_gcc_builtin_va_arg);
  result.function().location()=expr.location();
  result.function().type()=new_type;
  result.arguments().push_back(arg);
  result.type()=new_type.return_type();
  
  expr.swap(result);
  
  // make sure symbol exists
  symbolt symbol;
  symbol.base_name=ID_gcc_builtin_va_arg;
  symbol.name=ID_gcc_builtin_va_arg;
  symbol.type=new_type;
  
  context.move(symbol);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_cw_va_arg_typeof

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_cw_va_arg_typeof(exprt &expr)
{
  // used in Code Warrior via
  //
  // __va_arg( <Symbol>, _var_arg_typeof( <Typ> ) )
  //
  // where __va_arg is declared as
  //
  // extern void* __va_arg(void*, int);

  typet &type=static_cast<typet &>(expr.add(ID_type_arg));
  typecheck_type(type);

  // these return an integer
  expr.type()=int_type();
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_builtin_offsetof

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_builtin_offsetof(exprt &expr)
{
  // these need not be constant, due to array indices!

  if(expr.operands().size()!=0)
  {
    err_location(expr);
    throw "builtin_offsetof expects no operands";
  }

  typet &type=static_cast<typet &>(expr.add(ID_type_arg));
  typecheck_type(type);
  
  exprt &member=static_cast<exprt &>(expr.add(ID_designator));

  exprt result=gen_zero(size_type());

  forall_operands(m_it, member)
  {
    if(type.id()==ID_symbol)
      type=follow(type);

    if(m_it->id()==ID_member)
    {
      if(type.id()!=ID_union && type.id()!=ID_struct)
      {
        err_location(expr);
        throw "offsetof of member expects struct/union type, "
              "but got `"+to_string(type)+"'";
      }
      
      bool found=false;
      irep_idt component_name=m_it->get(ID_component_name);

      while(!found)
      {
        assert(type.id()==ID_union || type.id()==ID_struct);
      
        const struct_union_typet &struct_union_type=
          to_struct_union_type(type);
          
        // direct member?
        if(struct_union_type.has_component(component_name))
        {
          found=true;

          if(type.id()==ID_struct)
          {
            exprt o=c_offsetof(to_struct_type(type), component_name, *this);

            if(o.is_nil())
            {
              err_location(expr);
              str << "offsetof failed to determine offset of `"
                  << component_name << "'";
              throw 0;
            }
          
            if(o.type()!=size_type())
              o.make_typecast(size_type());

            result=plus_exprt(result, o);
          }
          
          type=struct_union_type.get_component(component_name).type();
        }
        else
        {
          // maybe anonymous?
          
          const struct_union_typet::componentst &components=
            struct_union_type.components();
            
          bool found2=false;
        
          for(struct_union_typet::componentst::const_iterator
              c_it=components.begin();
              c_it!=components.end();
              c_it++)
          {
            if(c_it->get_anonymous())
            {
              if(has_component_rec(c_it->type(), component_name, *this))
              {
                if(type.id()==ID_struct)
                {
                  exprt o=c_offsetof(to_struct_type(type), c_it->get_name(), *this);

                  if(o.is_nil())
                  {
                    err_location(expr);
                    str << "offsetof failed to determine offset of `"
                        << component_name << "'";
                    throw 0;
                  }
                
                  if(o.type()!=size_type())
                    o.make_typecast(size_type());

                  result=plus_exprt(result, o);
                }

                typet tmp=follow(c_it->type());
                type=tmp;
                assert(type.id()==ID_union || type.id()==ID_struct);
                found2=true;
                break; // we run into another iteration of the outer loop
              }
            }
          }
         
          if(!found2)
          {
            err_location(expr);    
            throw "offset-of of member failed to find component `"+
                  id2string(component_name)+"' in `"+to_string(type)+"'";
          }
        }
      }
    }
    else if(m_it->id()==ID_index)
    {
      assert(m_it->operands().size()==1);
      
      if(type.id()!=ID_array)
      {
        err_location(expr);
        throw "offsetof of index expects array type";
      }

      exprt index=m_it->op0();

      // still need to typecheck index
      typecheck_expr(index);

      exprt sub_size=c_sizeof(type.subtype(), *this);
      if(index.type()!=size_type()) index.make_typecast(size_type());
      result=plus_exprt(result, mult_exprt(sub_size, index));

      typet tmp=type.subtype();
      type=tmp;
    }
  }

  // We make an effort to produce a constant,
  // but this may depend on variables
  simplify(result, *this);
  result.location()=expr.location();

  expr.swap(result);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_operands(exprt &expr)
{
  if(expr.id()==ID_sideeffect &&
     expr.get(ID_statement)==ID_function_call)
  {
    // don't do function operand
    assert(expr.operands().size()==2);

    typecheck_expr(expr.op1()); // arguments
  }
  else if(expr.id()==ID_sideeffect &&
          expr.get(ID_statement)==ID_statement_expression)
  {
    typecheck_code(to_code(expr.op0()));
  }
  else if(expr.id()==ID_forall || expr.id()==ID_exists)
  {
    typecheck_decl(to_code(expr.op0().op0()));
    typecheck_expr(expr.op1());
  }
  else
  {
    Forall_operands(it, expr)
      typecheck_expr(*it);
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_symbol(exprt &expr)
{
  // first add prefix
  {
    symbol_exprt &symbol_expr=to_symbol_expr(expr);
    symbol_expr.set_identifier(add_language_prefix(symbol_expr.get_identifier()));
  }

  // adjust identifier, if needed
  replace_symbol(expr);
  
  const irep_idt &identifier=to_symbol_expr(expr).get_identifier();

  // look it up
  const symbolt *symbol_ptr;
  if(lookup(identifier, symbol_ptr))
  {
    err_location(expr);
    str << "failed to find symbol `" << identifier << "'";
    throw 0;
  }
  
  const symbolt &symbol=*symbol_ptr;

  if(symbol.is_type)
  {
    err_location(expr);
    str << "did not expect a type symbol here, but got `"
        << symbol.display_name() << "'";
    throw 0;
  }

  // save location
  locationt location=expr.location();

  if(symbol.is_macro)
  {
    expr=symbol.value;

    // put it back
    expr.location()=location;
  }
  else if(has_prefix(id2string(identifier), CPROVER_PREFIX "constant_infinity"))
  {
    expr=infinity_exprt(symbol.type);

    // put it back
    expr.location()=location;
  }
  else if(identifier=="c::__func__" ||
          identifier=="c::__FUNCTION__" ||
          identifier=="c::__PRETTY_FUNCTION__")
  {
    // __func__ is an ANSI-C standard compliant hack to get the function name
    // __FUNCTION__ and __PRETTY_FUNCTION__ are GCC-specific
    string_constantt s;
    s.set_value(location.get_function());
    s.location()=location;
    s.set(ID_C_lvalue, true);
    expr.swap(s);
  }
  else
  {
    expr=symbol_expr(symbol);

    // put it back
    expr.location()=location;

    if(symbol.is_lvalue)
      expr.set(ID_C_lvalue, true);

    if(expr.type().id()==ID_code) // function designator
    { // special case: this is sugar for &f
      exprt tmp(ID_address_of, pointer_typet());
      tmp.set("#implicit", true);
      tmp.type().subtype()=expr.type();
      tmp.location()=expr.location();
      tmp.move_to_operands(expr);
      expr.swap(tmp);
    }
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_side_effect_statement_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_side_effect_statement_expression(
  side_effect_exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "statement expression expects one operand";
    throw 0;
  }

  codet &code=to_code(expr.op0());

  assert(code.get(ID_statement)==ID_block);

  // the type is the type of the last statement in the
  // block, but do worry about labels!
  
  codet *last=&code;
  
  while(true)
  {
    const irep_idt &statement=last->get_statement();
    
    if(statement==ID_block)
    {
      if(last->operands().size()==0)
      {
        expr.type()=typet(ID_empty);
        return;
      }
      
      last=&to_code(last->operands().back());
    }
    else if(statement==ID_label)
    {
      assert(last->operands().size()==1);
      last=&(to_code(last->op0()));
    }
    else
      break;
  }
  
  irep_idt last_statement=last->get_statement();

  if(last_statement==ID_expression)
  {
    assert(last->operands().size()==1);
    expr.type()=last->op0().type();
  }
  else if(last_statement==ID_function_call)
  {
    // make the last statement an expression

    code_function_callt &fc=to_code_function_call(*last);

    side_effect_expr_function_callt sideeffect;

    sideeffect.function()=fc.function();
    sideeffect.arguments()=fc.arguments();
    sideeffect.location()=fc.location();

    sideeffect.type()=
      static_cast<const typet &>(fc.function().type().find(ID_return_type));

    expr.type()=sideeffect.type();

    if(fc.lhs().is_nil())
    {
      codet code_expr(ID_expression);
      code_expr.location() = fc.location();
      code_expr.move_to_operands(sideeffect);
      last->swap(code_expr);
    }
    else
    {
      codet code_expr(ID_expression);
      code_expr.location() = fc.location();

      exprt assign(ID_sideeffect);
      assign.set(ID_statement, ID_assign);
      assign.location()=fc.location();
      assign.move_to_operands(fc.lhs(), sideeffect);
      assign.type()=assign.op1().type();

      code_expr.move_to_operands(assign);
      last->swap(code_expr);
    }
  }
  else
    expr.type()=typet(ID_empty);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_sizeof

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_sizeof(exprt &expr)
{
  typet type;

  if(expr.operands().size()==0)
  {
    type.swap(static_cast<typet &>(expr.add(ID_type_arg)));
    typecheck_type(type);
  }
  else if(expr.operands().size()==1)
  {
    type.swap(expr.op0().type());
  }
  else
  {
    err_location(expr);
    str << "sizeof operator expects zero or one operand, "
           "but got " << expr.operands().size();
    throw 0;
  }

  exprt new_expr=c_sizeof(type, *this);

  if(new_expr.is_nil())
  {
    err_location(expr);
    str << "type has no size: "
        << to_string(type);
    throw 0;
  }

  new_expr.swap(expr);

  expr.add(ID_C_c_sizeof_type)=type;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_alignof

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_alignof(exprt &expr)
{
  typet argument_type;

  if(expr.operands().size()==1)
    argument_type=expr.op0().type();
  else
  {
    typet &op_type=static_cast<typet &>(expr.add(ID_type_arg));
    typecheck_type(op_type);
    argument_type=op_type;
  }

  // we only care about the type
  unsigned a=alignment(argument_type, *this);
  
  exprt tmp=from_integer(a, size_type());
  tmp.location()=expr.location();
  
  expr.swap(tmp);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_typecast(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "typecast operator expects one operand";
    throw 0;
  }

  exprt &op=expr.op0();

  typecheck_type(expr.type());
  
  {
    // first clean the type of any side-effects
    std::list<codet> clean_code;
    clean_type(irep_idt(), expr.type(), clean_code);

    if(!clean_code.empty())
    {
      sideeffect_exprt sideeffect_expr(ID_statement_expression, empty_typet());
      sideeffect_expr.copy_to_operands(code_blockt(clean_code));
    
      // We merge the side-effect into the operand, using
      // a comma-expression.
      // I.e., (type)e becomes (type)(side-effect, e)
    
      exprt comma_expr(ID_comma, op.type());
      comma_expr.copy_to_operands(sideeffect_expr, op);
      op.swap(comma_expr);
    }
  }

  const typet expr_type=follow(expr.type());

  if(expr_type.id()==ID_union &&
     !base_type_eq(expr_type, op.type(), *this) &&
     op.id()!=ID_initializer_list)
  {
    // This is a GCC extension. It's either a 'temporary union',
    // where the argument is one of the member types.
    
    // This is one of the few places where it's detectable
    // that we are using "bool" for boolean operators instead
    // of "int". We convert for this reason.
    if(follow(op.type()).id()==ID_bool)
      op.make_typecast(int_type());

    // we need to find a member with the right type
    const union_typet &union_type=to_union_type(expr_type);
    const union_typet::componentst &components=union_type.components();
  
    for(union_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      if(base_type_eq(it->type(), op.type(), *this))
      {
        // found! build union constructor
        union_exprt union_expr(union_type);
        union_expr.location()=expr.location();
        union_expr.op()=op;
        union_expr.set_component_name(it->get_name());
        expr=union_expr;
        expr.set(ID_C_lvalue, true);
        return;
      }
    }
    
    // not found, complain
    err_location(expr);
    str << "type cast to union: type `"
        << to_string(op.type()) << "' not found in union";
    throw 0;
  }

  // We allow (TYPE){ expression }
  if(op.id()==ID_initializer_list)
  {
    // just do a normal initialization
    do_initializer(op, expr_type, false);

    exprt tmp=op;
    expr=tmp;
    expr.set(ID_C_lvalue, true);
    return;
  }
  
  // a cast to void is always fine
  if(expr_type.id()==ID_empty)
    return;

  const typet op_type=follow(op.type());
  
  // vectors?
  
  if(expr_type.id()==ID_vector)
  {
    // we are generous -- any vector to vector is fine
    if(op_type.id()==ID_vector)
      return;
    else if(op_type.id()==ID_signedbv ||
            op_type.id()==ID_unsignedbv)
      return;
  }
  
  // cast to same type?
  if(base_type_eq(expr_type, op_type, *this))
    return; // it's ok
  
  if(!is_number(expr_type) &&
     expr_type.id()!=ID_bool &&
     expr_type.id()!=ID_pointer &&
     expr_type.id()!=ID_array &&
     expr_type.id()!=ID_c_enum &&
     expr_type.id()!=ID_incomplete_c_enum)
  {
    err_location(expr);
    str << "type cast to `"
        << to_string(expr_type) << "' from `"
        << to_string(op_type) << "' not permitted";
    throw 0;
  }

  // Casts to booleans have particular meaning
  if(expr_type.get(ID_C_c_type)==ID_bool)
  {
    // we replace (_Bool)x by x!=0; use ieee_float_notequal for floats
    irep_idt id=
      op_type.id()==ID_floatbv?ID_ieee_float_notequal:ID_notequal;

    binary_exprt comparison(expr.op0(), id, gen_zero(expr.op0().type()), bool_typet());

    comparison.location()=expr.location();
    expr.swap(comparison);
    return;
  }

  if(is_number(op_type) ||
     op_type.id()==ID_c_enum ||
     op_type.id()==ID_incomplete_c_enum ||
     op_type.id()==ID_bool ||
     op_type.id()==ID_pointer)
  {
  }
  else if(op_type.id()==ID_array)
  {
    index_exprt index;
    index.array()=op;
    index.index()=gen_zero(index_type());
    index.type()=op_type.subtype();
    op=address_of_exprt(index);
  }
  else if(op_type.id()==ID_empty)
  {
    if(expr_type.id()!=ID_empty)
    {
      err_location(expr);
      str << "type cast from void only permitted to void, but got `"
          << to_string(expr.type()) << "'";
      throw 0;
    }
  }
  else if(op_type.id()==ID_vector)
  {
    // we are generous -- any vector to integer is fine
    if(expr_type.id()==ID_signedbv ||
       expr_type.id()==ID_unsignedbv)
      return;
  }
  else
  {
    err_location(expr);
    str << "type cast from `"
        << to_string(op_type) << "' not permitted";
    throw 0;
  }

  // special case: NULL

  if(expr_type.id()==ID_pointer &&
     op.is_zero())
  {
    // zero typecasted to a pointer is NULL
    expr.id(ID_constant);
    expr.set(ID_value, ID_NULL);
    expr.remove(ID_operands);
    return;
  }

  // The new thing is an lvalue if the previous one is
  // an lvalue, and it's just a pointer type cast.
  // This isn't really standard conformant!

  // Note that gcc says "warning: target of assignment not really an lvalue;
  // this will be a hard error in the future", i.e., we
  // can hope that the below will one day go away.
  
  // Current versions of gcc in fact do not do this! Yay!
  
  if(expr.op0().get_bool(ID_C_lvalue))
  {
    if(expr_type.id()==ID_pointer)
      expr.set(ID_C_lvalue, true);
  }
}

/*******************************************************************\

Function: c_typecheck_baset::make_index_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::make_index_type(exprt &expr)
{
  implicit_typecast(expr, index_type());
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_index(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id()
        << "' expects two operands";
    throw 0;
  }

  exprt &array_expr=expr.op0();
  exprt &index_expr=expr.op1();

  // we might have to swap them

  {
    const typet &array_full_type=follow(array_expr.type());
    const typet &index_full_type=follow(index_expr.type());

    if(array_full_type.id()!=ID_array &&
       array_full_type.id()!=ID_pointer &&
       (index_full_type.id()==ID_array ||
        index_full_type.id()==ID_pointer))
      std::swap(array_expr, index_expr);
  }

  make_index_type(index_expr);

  const typet &final_array_type=follow(array_expr.type());
  
  if(final_array_type.id()==ID_array)
  {
    if(array_expr.get_bool(ID_C_lvalue))
      expr.set(ID_C_lvalue, true);
  }
  else if(final_array_type.id()==ID_pointer)
  {
    // p[i] is syntactic sugar for *(p+i)

    typecheck_arithmetic_pointer(expr.op0());
    exprt addition(ID_plus, array_expr.type());
    addition.operands().swap(expr.operands());
    expr.move_to_operands(addition);
    expr.id(ID_dereference);
    expr.set(ID_C_lvalue, true);
  }
  else
  {
    err_location(expr);
    str << "operator [] must take array or pointer but got `"
        << to_string(array_expr.type()) << "'";
    throw 0;
  }

  expr.type()=final_array_type.subtype();
}

/*******************************************************************\

Function: c_typecheck_baset::adjust_float_rel

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::adjust_float_rel(exprt &expr)
{
  // equality and disequality on float is not mathematical equality!
  assert(expr.operands().size()==2);

  if(follow(expr.op0().type()).id()==ID_floatbv)
  {
    if(expr.id()==ID_equal)
      expr.id(ID_ieee_float_equal);
    else if(expr.id()==ID_notequal)
      expr.id(ID_ieee_float_notequal);
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_rel

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_rel(exprt &expr)
{
  expr.type()=typet(ID_bool);

  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id()
        << "' expects two operands";
    throw 0;
  }

  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet o_type0=op0.type();
  const typet o_type1=op1.type();

  if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    if(follow(o_type0)==follow(o_type1))
    {
      const typet &final_type=follow(o_type0);
      if(final_type.id()!=ID_array &&
         final_type.id()!=ID_incomplete_struct)
      {
        adjust_float_rel(expr);
        return; // no promotion necessary
      }
    }
  }

  implicit_typecast_arithmetic(op0, op1);

  const typet &type0=op0.type();
  const typet &type1=op1.type();

  if(type0==type1)
  {
    if(is_number(type0))
    {
      adjust_float_rel(expr);
      return;
    }

    if(type0.id()==ID_pointer)
    {
      if(expr.id()==ID_equal || expr.id()==ID_notequal)
        return;

      if(expr.id()==ID_le || expr.id()==ID_lt ||
         expr.id()==ID_ge || expr.id()==ID_gt)
        return;
    }

    if(type0.id()==ID_string_constant)
    {
      if(expr.id()==ID_equal || expr.id()==ID_notequal)
        return;
    }
  }
  else
  {
    // pointer and zero
    if(type0.id()==ID_pointer && op1.is_zero())
    {
      op1=constant_exprt(type0);
      op1.set(ID_value, ID_NULL);
      return;
    }

    if(type1.id()==ID_pointer && op0.is_zero())
    {
      op0=constant_exprt(type1);
      op0.set(ID_value, ID_NULL);
      return;
    }

    // pointer and integer
    if(type0.id()==ID_pointer && is_number(type1))
    {
      op1.make_typecast(type0);
      return;
    }

    if(type1.id()==ID_pointer && is_number(type0))
    {
      op0.make_typecast(type1);
      return;
    }

    if(type0.id()==ID_pointer && type1.id()==ID_pointer)
    {
      op1.make_typecast(type0);
      return;
    }
  }

  err_location(expr);
  str << "operator `" << expr.id()
      << "' not defined for types `"
      << to_string(o_type0) << "' and `"
      << to_string(o_type1) << "'";
  throw 0;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_ptrmember

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_ptrmember(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error("ptrmember operator expects one operand");
    throw 0;
  }

  const typet &final_op0_type=follow(expr.op0().type());

  if(final_op0_type.id()!=ID_pointer &&
     final_op0_type.id()!=ID_array)
  {
    err_location(expr);
    str << "ptrmember operator requires pointer type "
           "on left hand side, but got `"
        << to_string(expr.op0().type()) << "'";
    throw 0;
  }

  // turn x->y into (*x).y

  exprt deref(ID_dereference);
  deref.move_to_operands(expr.op0());
  deref.location()=expr.location();

  typecheck_expr_dereference(deref);

  expr.op0().swap(deref);

  expr.id(ID_member);
  typecheck_expr_member(expr);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_member(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error("member operator expects one operand");
    throw 0;
  }

  exprt &op0=expr.op0();
  typet type=op0.type();

  follow_symbol(type);
  
  if(type.id()==ID_incomplete_struct)
  {
    err_location(expr);
    str << "member operator got incomplete structure type "
           "on left hand side";
    throw 0;
  }

  if(type.id()!=ID_struct &&
     type.id()!=ID_union)
  {
    err_location(expr);
    str << "member operator requires structure type "
           "on left hand side but got `"
        << to_string(type) << "'";
    throw 0;
  }
  
  const struct_union_typet &struct_union_type=
    to_struct_union_type(type);

  const irep_idt &component_name=
    expr.get(ID_component_name);

  // first try to find directly
  struct_union_typet::componentt component=
    struct_union_type.get_component(component_name);

  // if that fails, search the anonymous members

  if(component.is_nil())
  {
    exprt tmp=get_component_rec(op0, component_name, *this);

    if(tmp.is_nil())
    {
      // give up
      err_location(expr);
      str << "member `" << component_name
          << "' not found in `"
          << to_string(type) << "'";
      throw 0;
    }
    
    // done!
    expr.swap(tmp);
    return;
  }

  expr.type()=component.type();

  if(op0.get_bool(ID_C_lvalue))
    expr.set(ID_C_lvalue, true);

  if(op0.get_bool(ID_C_constant) || type.get_bool(ID_C_constant))
    expr.set(ID_C_constant, true);

  // copy method identifier
  const irep_idt &identifier=component.get(ID_C_identifier);

  if(identifier!=irep_idt())
    expr.set(ID_C_identifier, identifier);

  const irep_idt &access=component.get_access();

  if(access==ID_private)
  {
    err_location(expr);
    str << "member `" << component_name
        << "' is " << access;
    throw 0;
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_trinary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_trinary(if_exprt &expr)
{
  exprt::operandst &operands=expr.operands();

  assert(operands.size()==3);

  // copy (save) original types
  const typet o_type0=operands[0].type();
  const typet o_type1=operands[1].type();
  const typet o_type2=operands[2].type();

  implicit_typecast_bool(operands[0]);
  implicit_typecast_arithmetic(operands[1], operands[2]);

  if(operands[1].type().id()==ID_pointer &&
     operands[2].type().id()!=ID_pointer)
    implicit_typecast(operands[2], operands[1].type());
  else if(operands[2].type().id()==ID_pointer &&
          operands[1].type().id()!=ID_pointer)
    implicit_typecast(operands[1], operands[2].type());

  if(operands[1].type().id()==ID_pointer &&
     operands[2].type().id()==ID_pointer &&
     operands[1].type()!=operands[2].type())
  {
    // make it void *
    expr.type()=typet(ID_pointer);
    expr.type().subtype()=typet(ID_empty);
    implicit_typecast(operands[1], expr.type());
    implicit_typecast(operands[2], expr.type());
  }

  if(operands[1].type().id()==ID_empty ||
     operands[2].type().id()==ID_empty)
  {
    expr.type()=empty_typet();
    return;
  }

  if(follow(operands[1].type())==follow(operands[2].type()))
  {
    expr.type()=operands[1].type();
    
    // GCC says: "A conditional expression is a valid lvalue
    // if its type is not void and the true and false branches
    // are both valid lvalues."
    
    if(operands[1].get_bool(ID_C_lvalue) &&
       operands[2].get_bool(ID_C_lvalue))
      expr.set(ID_C_lvalue, true);
    
    return;
  }

  err_location(expr);
  str << "operator ?: not defined for types `"
      << to_string(o_type1) << "' and `"
      << to_string(o_type2) << "'";
  throw 0;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_side_effect_gcc_conditional_expresssion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_side_effect_gcc_conditional_expression(
  side_effect_exprt &expr)
{
  // x ? : y is almost the same as x ? x : y,
  // but not quite, as x is evaluated only once

  exprt::operandst &operands=expr.operands();

  if(operands.size()!=2)
  {
    err_location(expr);
    error("gcc conditional_expr expects two operands");
    throw 0;
  }

  // use typechecking code for "if"

  if_exprt if_expr;
  if_expr.cond()=operands[0];
  if_expr.true_case()=operands[0];
  if_expr.false_case()=operands[1];
  if_expr.location()=expr.location();

  typecheck_expr_trinary(if_expr);

  // copy the result
  expr.op0()=if_expr.op1();
  expr.op1()=if_expr.op2();
  expr.type()=if_expr.type();
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_address_of(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    error("unary operator & expects one operand");
    throw 0;
  }

  exprt &op=expr.op0();
  
  // special case: address of label
  if(op.id()==ID_label)
  {
    expr.type()=pointer_typet(empty_typet());
    return;
  }

  // special case: address of function designator
  // ANSI-C 99 section 6.3.2.1 paragraph 4

  if(op.id()==ID_address_of &&
     op.get_bool(ID_C_implicit) &&
     op.operands().size()==1 &&
     op.op0().type().id()==ID_code)
  {
    // make the implicit address_of an explicit address_of
    exprt tmp;
    tmp.swap(op);
    tmp.set(ID_C_implicit, false);
    expr.swap(tmp);
    return;
  }

  expr.type()=pointer_typet();

  if(op.id()==ID_struct ||
     op.id()==ID_union ||
     op.id()==ID_array ||
     op.id()==ID_string_constant)
  {
    // these are really objects
  }
  else if(op.get_bool(ID_C_lvalue))
  {
    // ok
  }
  else if(op.type().id()==ID_code)
  {
    // ok
  }
  else
  {
    err_location(expr);
    str << "address_of error: `" << to_string(op)
        << "' not an lvalue";
    throw 0;
  }

  expr.type().subtype()=op.type();
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_dereference(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "unary operator * expects one operand";
    throw 0;
  }

  exprt &op=expr.op0();

  const typet op_type=follow(op.type());

  if(op_type.id()==ID_array)
  {
    // *a is the same as a[0]
    expr.id(ID_index);
    expr.type()=op_type.subtype();
    expr.copy_to_operands(gen_zero(index_type()));
    assert(expr.operands().size()==2);
  }
  else if(op_type.id()==ID_pointer)
  {
    expr.type()=op_type.subtype();
  }
  else
  {
    err_location(expr);
    str << "operand of unary * `" << to_string(op)
        << "' is not a pointer, but got `"
        << to_string(op_type) << "'";
    throw 0;
  }

  expr.set(ID_C_lvalue, true);

  // if you dereference a pointer pointing to
  // a function, you get a pointer again
  // allowing ******...*p

  typecheck_expr_function_identifier(expr);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_function_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_function_identifier(exprt &expr)
{
  if(expr.type().id()==ID_code)
  {
    exprt tmp(ID_address_of, pointer_typet());
    tmp.set(ID_C_implicit, true);
    tmp.type().subtype()=expr.type();
    tmp.location()=expr.location();
    tmp.move_to_operands(expr);
    expr.swap(tmp);
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_side_effect

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_side_effect(side_effect_exprt &expr)
{
  const irep_idt &statement=expr.get_statement();

  if(statement==ID_preincrement ||
     statement==ID_predecrement ||
     statement==ID_postincrement ||
     statement==ID_postdecrement)
  {
    if(expr.operands().size()!=1)
    {
      err_location(expr);
      str << statement << "operator expects one operand";
    }

    const exprt &op0=expr.op0();
    const typet &type0=op0.type();
    const typet &final_type0=follow(type0);

    if(!op0.get_bool(ID_C_lvalue))
    {
      err_location(op0);
      str << "prefix operator error: `" << to_string(op0)
          << "' not an lvalue";
      throw 0;
    }

    if(type0.get_bool(ID_C_constant))
    {
      err_location(op0);
      str << "error: `" << to_string(op0)
          << "' is constant";
      throw 0;
    }

    if(is_number(final_type0) ||
       final_type0.id()==ID_bool ||
       final_type0.id()==ID_c_enum ||
       final_type0.id()==ID_incomplete_c_enum)
    {
      expr.type()=type0;
    }
    else if(final_type0.id()==ID_pointer)
    {
      expr.type()=type0;
      typecheck_arithmetic_pointer(op0);
    }
    else
    {
      err_location(expr);
      str << "operator `" << statement
          << "' not defined for type `"
          << to_string(type0) << "'";
      throw 0;
    }
  }
  else if(has_prefix(id2string(statement), "assign"))
    typecheck_side_effect_assignment(expr);
  else if(statement==ID_function_call)
    typecheck_side_effect_function_call(to_side_effect_expr_function_call(expr));
  else if(statement==ID_statement_expression)
    typecheck_side_effect_statement_expression(expr);
  else if(statement==ID_gcc_conditional_expression)
    typecheck_side_effect_gcc_conditional_expression(expr);
  else
  {
    err_location(expr);
    str << "unknown side effect: " << statement;
    throw 0;
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_side_effect_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_side_effect_function_call(
  side_effect_expr_function_callt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    throw "function_call side effect expects two operands";
  }

  exprt &f_op=expr.function();

  // f_op is not yet typechecked, in contrast to the other arguments.
  // This is a big special case!

  if(f_op.id()==ID_symbol)
  {
    const irep_idt &identifier=
      add_language_prefix(to_symbol_expr(f_op).get_identifier());

    if(context.symbols.find(identifier)==context.symbols.end())
    {
      // This is an undeclared function. Let's just add it.
      // We do a bit of return-type guessing, but just a bit.
      typet return_type=int_type();
      
      // The following isn't really right and sound, but there
      // are too many idiots out there who use malloc and the like
      // without the right header file.
      if(identifier=="c::malloc" ||
         identifier=="c::realloc" ||
         identifier=="c::reallocf" ||
         identifier=="c::valloc")
        return_type=pointer_typet(empty_typet()); // void *

      symbolt new_symbol;

      new_symbol.name=identifier;
      new_symbol.base_name=std::string(id2string(identifier), 3, std::string::npos);
      new_symbol.location=expr.location();
      new_symbol.type=code_typet();
      new_symbol.type.set(ID_C_incomplete, true);
      new_symbol.type.add(ID_return_type)=return_type;

      // TODO: should also guess some argument types

      symbolt *symbol_ptr;
      move_symbol(new_symbol, symbol_ptr);

      err_location(f_op);
      str << "function `" << identifier << "' is not declared";
      warning();
    }
  }

  // typecheck it now
  typecheck_expr(f_op);

  const typet f_op_type=follow(f_op.type());

  if(f_op_type.id()!=ID_pointer)
  {
    err_location(f_op);
    str << "expected function/function pointer as argument but got `"
        << to_string(f_op_type) << "'";
    throw 0;
  }

  // do implicit dereference
  if(f_op.id()==ID_address_of &&
     f_op.get_bool(ID_C_implicit) &&
     f_op.operands().size()==1)
  {
    exprt tmp;
    tmp.swap(f_op.op0());
    f_op.swap(tmp);
  }
  else
  {
    exprt tmp(ID_dereference, f_op_type.subtype());
    tmp.set(ID_C_implicit, true);
    tmp.location()=f_op.location();
    tmp.move_to_operands(f_op);
    f_op.swap(tmp);
  }

  if(f_op.type().id()!=ID_code)
  {
    err_location(f_op);
    throw "expected code as argument";
  }

  const code_typet &code_type=to_code_type(f_op.type());
  
  expr.type()=code_type.return_type();

  typecheck_function_call_arguments(expr);

  do_special_functions(expr);
}

/*******************************************************************\

Function: c_typecheck_baset::do_special_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::do_special_functions(
  side_effect_expr_function_callt &expr)
{
  const exprt &f_op=expr.function();
  const locationt &location=expr.location();

  // some built-in functions
  if(f_op.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(f_op).get_identifier();

    if(identifier==CPROVER_PREFIX "same_object")
    {
      if(expr.arguments().size()!=2)
      {
        err_location(f_op);
        throw "same_object expects two operands";
      }

      exprt same_object_expr("same-object", bool_typet());
      same_object_expr.operands()=expr.arguments();
      same_object_expr.location()=location;
      expr.swap(same_object_expr);
    }
    else if(identifier==CPROVER_PREFIX "buffer_size")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "buffer_size expects one operand";
      }

      exprt buffer_size_expr("buffer_size", uint_type());
      buffer_size_expr.operands()=expr.arguments();
      buffer_size_expr.location()=location;
      expr.swap(buffer_size_expr);
    }
    else if(identifier==CPROVER_PREFIX "is_zero_string")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "is_zero_string expects one operand";
      }

      exprt is_zero_string_expr("is_zero_string", bool_typet());
      is_zero_string_expr.operands()=expr.arguments();
      is_zero_string_expr.set(ID_C_lvalue, true); // make it an lvalue
      is_zero_string_expr.location()=location;
      expr.swap(is_zero_string_expr);
    }
    else if(identifier==CPROVER_PREFIX "zero_string_length")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "zero_string_length expects one operand";
      }

      exprt zero_string_length_expr("zero_string_length", uint_type());
      zero_string_length_expr.operands()=expr.arguments();
      zero_string_length_expr.set(ID_C_lvalue, true); // make it an lvalue
      zero_string_length_expr.location()=location;
      expr.swap(zero_string_length_expr);
    }
    else if(identifier==CPROVER_PREFIX "DYNAMIC_OBJECT")
    {
      if(expr.arguments().size()!=1)
        throw "dynamic_object expects one argument";

      exprt dynamic_object_expr=exprt(ID_dynamic_object, expr.type());
      dynamic_object_expr.operands()=expr.arguments();
      dynamic_object_expr.location()=location;
      expr.swap(dynamic_object_expr);
    }
    else if(identifier==CPROVER_PREFIX "POINTER_OFFSET")
    {
      if(expr.arguments().size()!=1)
        throw "pointer_offset expects one argument";

      exprt pointer_offset_expr=exprt(ID_pointer_offset, expr.type());
      pointer_offset_expr.operands()=expr.arguments();
      pointer_offset_expr.location()=location;
      expr.swap(pointer_offset_expr);
    }
    else if(identifier==CPROVER_PREFIX "POINTER_OBJECT")
    {
      if(expr.arguments().size()!=1)
        throw "pointer_object expects one argument";

      exprt pointer_object_expr=exprt(ID_pointer_object, expr.type());
      pointer_object_expr.operands()=expr.arguments();
      pointer_object_expr.location()=location;
      expr.swap(pointer_object_expr);
    }
    else if(identifier==CPROVER_PREFIX "isnan")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "isnan expects one operand";
      }

      exprt isnan_expr(ID_isnan, bool_typet());
      isnan_expr.operands()=expr.arguments();
      isnan_expr.location()=location;
      expr.swap(isnan_expr);
    }
    else if(identifier==CPROVER_PREFIX "isfinite")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "isfinite expects one operand";
      }

      exprt isfinite_expr(ID_isfinite, bool_typet());
      isfinite_expr.operands()=expr.arguments();
      isfinite_expr.location()=location;
      expr.swap(isfinite_expr);
    }
    else if(identifier==CPROVER_PREFIX "inf")
    {
      constant_exprt inf_expr=
        ieee_floatt::plus_infinity(ieee_float_spect::double_precision()).to_expr();
      inf_expr.location()=location;
      expr.swap(inf_expr);
    }
    else if(identifier==CPROVER_PREFIX "inff")
    {
      constant_exprt inff_expr=
        ieee_floatt::plus_infinity(ieee_float_spect::single_precision()).to_expr();
      inff_expr.location()=location;
      expr.swap(inff_expr);
    }
    else if(identifier==CPROVER_PREFIX "infl")
    {
      floatbv_typet type=to_floatbv_type(long_double_type());
      constant_exprt infl_expr=
        ieee_floatt::plus_infinity(ieee_float_spect(type)).to_expr();
      infl_expr.location()=location;
      expr.swap(infl_expr);
    }
    else if(identifier==CPROVER_PREFIX "abs" ||
            identifier==CPROVER_PREFIX "labs" ||
            identifier==CPROVER_PREFIX "fabs" ||
            identifier==CPROVER_PREFIX "fabsf" ||
            identifier==CPROVER_PREFIX "fabsl")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "abs-functions expect one operand";
      }

      exprt abs_expr(ID_abs, expr.type());
      abs_expr.operands()=expr.arguments();
      abs_expr.location()=location;
      expr.swap(abs_expr);
    }
    else if(identifier==CPROVER_PREFIX "malloc")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "malloc expects one operand";
      }

      exprt malloc_expr=side_effect_exprt(ID_malloc);
      malloc_expr.type()=expr.type();
      malloc_expr.location()=location;
      malloc_expr.operands()=expr.arguments();
      expr.swap(malloc_expr);
    }
    else if(identifier==CPROVER_PREFIX "isinf")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "isinf expects one operand";
      }

      exprt isinf_expr(ID_isinf, bool_typet());
      isinf_expr.operands()=expr.arguments();
      isinf_expr.location()=location;
      expr.swap(isinf_expr);
    }
    else if(identifier==CPROVER_PREFIX "isnormal")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "isnormal expects one operand";
      }

      exprt isnormal_expr(ID_isnormal, bool_typet());
      isnormal_expr.operands()=expr.arguments();
      isnormal_expr.location()=location;
      expr.swap(isnormal_expr);
    }
    else if(identifier==CPROVER_PREFIX "sign")
    {
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "sign expects one operand";
      }

      exprt sign_expr(ID_sign, bool_typet());
      sign_expr.operands()=expr.arguments();
      sign_expr.location()=location;
      expr.swap(sign_expr);
    }
    else if(identifier==CPROVER_PREFIX "equal")
    {
      if(expr.arguments().size()!=2)
      {
        err_location(f_op);
        throw "equal expects two operands";
      }
      
      equal_exprt equality_expr;
      equality_expr.operands()=expr.arguments();
      equality_expr.location()=location;
      
      if(!base_type_eq(equality_expr.lhs().type(),
                       equality_expr.rhs().type(), *this))
      {
        err_location(f_op);
        throw "equal expects two operands of same type";
      }

      expr.swap(equality_expr);
    }
    else if(identifier=="c::__builtin_expect")
    {
      // this is a gcc extension to provide branch prediction
      if(expr.arguments().size()!=2)
      {
        err_location(f_op);
        throw "__builtin_expect expects two arguments";
      }

      exprt tmp=expr.arguments()[0];
      expr.swap(tmp);
    }
    else if(identifier=="c::__builtin_object_size")
    {
      // this is a gcc extension to provide information about
      // object sizes at compile time
      // http://gcc.gnu.org/onlinedocs/gcc/Object-Size-Checking.html
      
      if(expr.arguments().size()!=2)
      {
        err_location(f_op);
        throw "__builtin_object_size expects two arguments";
      }

      make_constant(expr.arguments()[1]);
      
      mp_integer arg1;
      
      if(expr.arguments()[1].is_true())
        arg1=1;
      else if(expr.arguments()[1].is_false())
        arg1=0;
      else if(to_integer(expr.arguments()[1], arg1))
      {
        err_location(f_op);
        str << "__builtin_object_size expects constant as second argument, but got "
            << to_string(expr.arguments()[1]);
        throw 0;
      }

      exprt tmp;

      // the followin means "don't know"      
      if(arg1==0 || arg1==1)
      {
        tmp=from_integer(-1, size_type());
        tmp.location()=f_op.location();
      }
      else
      {
        tmp=from_integer(0, size_type());
        tmp.location()=f_op.location();
      }
      
      tmp.swap(expr);
    }
    else if(identifier=="c::__builtin_choose_expr")
    {
      // this is a gcc extension similar to ?:
      if(expr.arguments().size()!=3)
      {
        err_location(f_op);
        throw "__builtin_choose_expr expects three arguments";
      }
      
      expr.arguments()[0].make_typecast(bool_typet());
      make_constant(expr.arguments()[0]);
      
      if(expr.arguments()[0].is_true())
      {
        exprt tmp=expr.arguments()[1];
        expr.swap(tmp);
      }
      else
      {
        exprt tmp=expr.arguments()[2];
        expr.swap(tmp);
      }
    }
    else if(identifier=="c::__builtin_constant_p")
    {
      // this is a gcc extension to tell whether the argument
      // is known to be a compile-time constant
      if(expr.arguments().size()!=1)
      {
        err_location(f_op);
        throw "__builtin_constant_p expects one argument";
      }

      // try to produce constant
      exprt tmp1=expr.arguments().front();
      simplify(tmp1, *this);

      exprt tmp2=from_integer(tmp1.is_constant(), expr.type());      
      tmp2.location()=location;
      expr.swap(tmp2);
    }
    else if(identifier==CPROVER_PREFIX "float_debug1" ||
            identifier==CPROVER_PREFIX "float_debug2")
    {
      if(expr.arguments().size()!=2)
      {
        err_location(f_op);
        throw "float_debug expects two operands";
      }

      const irep_idt &id=
        identifier==CPROVER_PREFIX "float_debug1"?
        "float_debug1":"float_debug2";
      exprt float_debug_expr(id, expr.type());
      float_debug_expr.operands()=expr.arguments();
      float_debug_expr.location()=location;
      expr.swap(float_debug_expr);
    }
    else if(identifier=="c::__sync_fetch_and_add" ||
            identifier=="c::__sync_fetch_and_sub" ||
            identifier=="c::__sync_fetch_and_or" ||
            identifier=="c::__sync_fetch_and_and" ||
            identifier=="c::__sync_fetch_and_xor" ||
            identifier=="c::__sync_fetch_and_nand" ||
            identifier=="c::__sync_add_and_fetch" ||
            identifier=="c::__sync_sub_and_fetch" ||
            identifier=="c::__sync_or_and_fetch" ||
            identifier=="c::__sync_and_and_fetch" ||
            identifier=="c::__sync_xor_and_fetch" ||
            identifier=="c::__sync_nand_and_fetch" ||
            identifier=="c::__sync_val_compare_and_swap" ||
            identifier=="c::__sync_lock_test_and_set" ||
            identifier=="c::__sync_lock_release")
    {
      // These are polymorphic, see
      // http://gcc.gnu.org/onlinedocs/gcc-4.1.1/gcc/Atomic-Builtins.html
      
      // adjust return type of function to match pointer subtype
      if(expr.arguments().size()<1)
      {
        err_location(f_op);
        throw "__sync_* primitives take as least one argument";
      }
      
      exprt &ptr_arg=expr.arguments().front();

      if(ptr_arg.type().id()!=ID_pointer)
      {
        err_location(f_op);
        throw "__sync_* primitives take pointer as first argument";
      }
      
      expr.type()=expr.arguments().front().type().subtype();
    }
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_function_call_arguments

  Inputs: type-checked arguments, type-checked function

 Outputs: type-adjusted function arguments

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_function_call_arguments(
  side_effect_expr_function_callt &expr)
{
  const exprt &f_op=expr.function();
  const code_typet &code_type=to_code_type(f_op.type());
  exprt::operandst &arguments=expr.arguments();
  const code_typet::argumentst &argument_types=
    code_type.arguments();
    
  // no. of arguments test

  if(code_type.get_bool(ID_C_incomplete))
  {
    // can't check
  }
  else if(code_type.is_KnR())
  {
    // We are generous on KnR; any number is ok.
    // We will in missing ones with "NIL".

    while(argument_types.size()>arguments.size())
      arguments.push_back(nil_exprt());
  }
  else if(code_type.has_ellipsis())
  {
    if(argument_types.size()>arguments.size())
    {
      err_location(expr);
      throw "not enough function arguments";
    }
  }
  else if(argument_types.size()!=arguments.size())
  {
    err_location(expr);
    str << "wrong number of function arguments: "
        << "expected " << argument_types.size()
        << ", but got " << arguments.size();
    throw 0;
  }
  
  for(unsigned i=0; i<arguments.size(); i++)
  {
    exprt &op=arguments[i];

    if(op.is_nil())
    {
      // ignore
    }
    else if(i<argument_types.size())
    {
      const code_typet::argumentt &argument_type=
        argument_types[i];

      const typet &op_type=argument_type.type();

      if(op_type.id()==ID_bool &&
         op.id()==ID_sideeffect &&
         op.get(ID_statement)==ID_assign &&
         op.type().id()!=ID_bool)
      {
        err_location(expr);
        warning("assignment where Boolean argument is expected");
      }

      implicit_typecast(op, op_type);
    }
    else
    {
      // don't know type, just do standard conversion
      
      const typet &type=follow(op.type());
      if(type.id()==ID_array)
      {
        pointer_typet dest_type;
        dest_type.subtype()=empty_typet();
        dest_type.subtype().set(ID_C_constant, ID_1);
        implicit_typecast(op, dest_type);
      }
    }
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_constant(exprt &expr)
{
  // nothing to do
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_unary_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_unary_arithmetic(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "operator `" << expr.id()
        << "' expects one operand";
    throw 0;
  }

  exprt &operand=expr.op0();
  
  const typet &o_type=follow(operand.type());

  if(o_type.id()==ID_vector)
  {
    if(is_number(follow(o_type.subtype())))
    {
      // Vector arithmetic.
      expr.type()=operand.type();
      return;
    }
  }

  implicit_typecast_arithmetic(operand);

  if(is_number(operand.type()))
  {
    expr.type()=operand.type();
    return;
  }

  err_location(expr);
  str << "operator `" << expr.id()
      << "' not defined for type `"
      << to_string(operand.type()) << "'";
  throw 0;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_unary_boolean

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_unary_boolean(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "operator `" << expr.id()
        << "' expects one operand";
    throw 0;
  }

  exprt &operand=expr.op0();

  implicit_typecast_bool(operand);
  
  // This is not quite accurate: the standard says the result
  // should be of type 'int'.
  // We do 'bool' anyway to get more compact formulae. Eventually,
  // this should be achieved by means of simplification, and not
  // in the frontend.
  expr.type()=typet(ID_bool);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_binary_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_binary_arithmetic(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id()
        << "' expects two operands";
    throw 0;
  }

  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet o_type0=follow(op0.type());
  const typet o_type1=follow(op1.type());

  if(o_type0.id()==ID_vector &&
     o_type1.id()==ID_vector)
  {
    if(follow(o_type0.subtype())==follow(o_type1.subtype()) &&
       is_number(follow(o_type0.subtype())))
    {
      // Vector arithmetic
      // Fairly strict typing rules, no promotion
      expr.type()=op0.type();
      return;
    }
  }

  // promote!
  
  implicit_typecast_arithmetic(op0, op1);

  const typet &type0=follow(op0.type());
  const typet &type1=follow(op1.type());

  if(expr.id()==ID_plus || expr.id()==ID_minus ||
     expr.id()==ID_mult || expr.id()==ID_div)
  {
    if(type0.id()==ID_pointer || type1.id()==ID_pointer)
    {
      typecheck_expr_pointer_arithmetic(expr);
      return;
    }
    else if(type0==type1)
    {
      if(is_number(type0))
      {
        expr.type()=type0;
        return;
      }
    }
  }
  else if(expr.id()==ID_mod)
  {
    if(type0==type1)
    {
      if(type0.id()==ID_signedbv || type0.id()==ID_unsignedbv)
      {
        expr.type()=type0;
        return;
      }
    }
  }
  else if(expr.id()==ID_bitand || 
          expr.id()==ID_bitxor ||
          expr.id()==ID_bitor)
  {
    if(type0==type1)
    {
      if(is_number(type0))
      {
        expr.type()=type0;
        return;
      }
      else if(type0.id()==ID_bool)
      {
        if(expr.id()==ID_bitand)
          expr.id(ID_and);
        else if(expr.id()==ID_bitor)
          expr.id(ID_or);
        else if(expr.id()==ID_bitxor)
          expr.id(ID_xor);
        else
          assert(false);
        expr.type()=type0;
        return;
      }
    }
  }

  err_location(expr);
  str << "operator `" << expr.id()
      << "' not defined for types `"
      << to_string(o_type0) << "' and `"
      << to_string(o_type1) << "'";
  throw 0;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_shifts

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_shifts(shift_exprt &expr)
{
  assert(expr.id()==ID_shl || expr.id()==ID_shr);
  
  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet o_type0=follow(op0.type());
  const typet o_type1=follow(op1.type());

  if(o_type0.id()==ID_vector &&
     o_type1.id()==ID_vector)
  {
    if(follow(o_type0.subtype())==follow(o_type1.subtype()) &&
       is_number(follow(o_type0.subtype())))
    {
      // {a0, a1, ..., an} >> {b0, b1, ..., bn} == {a0 >> b0, a1 >> b1, ..., an >> bn}
      // Fairly strict typing rules, no promotion
      expr.type()=op0.type();
      return;
    }
  }

  // must do the promotions _separately_!
  implicit_typecast_arithmetic(op0);
  implicit_typecast_arithmetic(op1);

  if(is_number(op0.type()) &&
     is_number(op1.type()))
  {
    expr.type()=op0.type();

    if(expr.id()==ID_shr) // shifting operation depends on types
    {
      const typet &op0_type=follow(op0.type());

      if(op0_type.id()==ID_unsignedbv)
      {
        expr.id(ID_lshr);
        return;
      }
      else if(op0_type.id()==ID_signedbv)
      {
        expr.id(ID_ashr);
        return;
      }
    }

    return;
  }

  err_location(expr);
  str << "operator `" << expr.id()
      << "' not defined for types `"
      << to_string(o_type0) << "' and `"
      << to_string(o_type1) << "'";
  throw 0;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_arithmetic_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_arithmetic_pointer(const exprt &expr)
{
  const typet &type=expr.type();
  assert(type.id()==ID_pointer);
  
  typet subtype=type.subtype();

  if(subtype.id()==ID_symbol)
    subtype=follow(subtype);
    
  if(subtype.id()==ID_incomplete_struct)
  {
    err_location(expr);
    throw "pointer arithmetic with unknown object size";
  }
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_pointer_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_pointer_arithmetic(exprt &expr)
{
  assert(expr.operands().size()==2);

  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  const typet &type0=op0.type();
  const typet &type1=op1.type();

  if(expr.id()==ID_minus ||
     (expr.id()==ID_sideeffect && expr.get(ID_statement)==ID_assign_minus))
  {
    if(type0.id()==ID_pointer &&
       type1.id()==ID_pointer)
    {
      // We should check the subtypes, and complain if
      // they are really different.
      expr.type()=pointer_diff_type();
      typecheck_arithmetic_pointer(op0);
      typecheck_arithmetic_pointer(op1);
      return;
    }

    if(type0.id()==ID_pointer &&
       (type1.id()==ID_bool ||
        type1.id()==ID_unsignedbv ||
        type1.id()==ID_signedbv ||
        type1.id()==ID_c_enum))
    {
      typecheck_arithmetic_pointer(op0);
      make_index_type(op1);
      expr.type()=type0;
      return;
    }
  }
  else if(expr.id()==ID_plus ||
          (expr.id()==ID_sideeffect && expr.get(ID_statement)==ID_assign_plus))
  {
    exprt *p_op, *int_op;

    if(type0.id()==ID_pointer)
    {
      p_op=&op0;
      int_op=&op1;
    }
    else if(type1.id()==ID_pointer)
    {
      p_op=&op1;
      int_op=&op0;
    }
    else
      assert(false);

    if(int_op->type().id()==ID_bool ||
       int_op->type().id()==ID_unsignedbv ||
       int_op->type().id()==ID_signedbv ||
       int_op->type().id()==ID_c_enum)
    {
      typecheck_arithmetic_pointer(*p_op);
      make_index_type(*int_op);
      expr.type()=p_op->type();
      return;
    }
  }

  err_location(expr);
  str << "operator `" << expr.id()
      << "' not defined for types `"
      << to_string(type0) << "' and `"
      << to_string(type1) << "'";
  throw 0;
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_expr_binary_boolean

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_expr_binary_boolean(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id()
        << "' expects two operands";
    throw 0;
  }

  implicit_typecast_bool(expr.op0());
  implicit_typecast_bool(expr.op1());

  // This is not quite accurate: the standard says the result
  // should be of type 'int'.
  // We do 'bool' anyway to get more compact formulae. Eventually,
  // this should be achieved by means of simplification, and not
  // in the frontend.
  expr.type()=typet(ID_bool);
}

/*******************************************************************\

Function: c_typecheck_baset::typecheck_side_effect_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::typecheck_side_effect_assignment(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.get(ID_statement)
        << "' expects two operands";
    throw 0;
  }
  
  const irep_idt &statement=expr.get(ID_statement);

  exprt &op0=expr.op0();
  exprt &op1=expr.op1();

  // se if we have a typecast on the LHS
  if(op0.id()==ID_typecast)
  {
    assert(op0.operands().size()==1);

    // set #lvalue and #constant
    op0.set(ID_C_lvalue, op0.op0().get_bool(ID_C_lvalue));
    op0.set(ID_C_constant, op0.op0().get_bool(ID_C_constant));
  }

  const typet o_type0=op0.type();
  const typet o_type1=op1.type();

  const typet &type0=op0.type();
  const typet &final_type0=follow(type0);

  expr.type()=type0;
  
  if(final_type0.id()==ID_empty)
  {
    err_location(expr);
    str << "cannot assign void";
    throw 0;
  }

  if(!op0.get_bool(ID_C_lvalue))
  {
    err_location(expr);
    str << "assignment error: `" << to_string(op0)
        << "' not an lvalue";
    throw 0;
  }

  if(o_type0.get_bool(ID_C_constant))
  {
    err_location(expr);
    str << "error: `" << to_string(op0)
        << "' is constant";
    throw 0;
  }
  
  // refuse to assign arrays
  if(final_type0.id()==ID_array ||
     final_type0.id()==ID_incomplete_array)
  {
    err_location(expr);
    str << "error: direct assignments to arrays not permitted";
    throw 0;
  }

  if(statement==ID_assign)
  {
    implicit_typecast(op1, o_type0);
    return;
  }
  else if(statement==ID_assign_shl ||
          statement==ID_assign_shr)
  {
    implicit_typecast_arithmetic(op1);

    if(is_number(op1.type()))
    {
      expr.type()=type0;

      if(statement==ID_assign_shl)
      {
        return;
      }
      else
      {
        if(final_type0.id()==ID_unsignedbv)
        {
          expr.set(ID_statement, ID_assign_lshr);
          return;
        }
        else if(final_type0.id()==ID_signedbv ||
                final_type0.id()==ID_c_enum)
        {
          expr.set(ID_statement, ID_assign_ashr);
          return;
        }
      }
    }
  }
  else
  {
    if(final_type0.id()==ID_pointer &&
       (statement==ID_assign_minus || statement==ID_assign_plus))
    {
      typecheck_expr_pointer_arithmetic(expr);
      return;
    }
    else if(final_type0.id()==ID_bool ||
            final_type0.id()==ID_c_enum ||
            final_type0.id()==ID_incomplete_c_enum)
    {
      implicit_typecast_arithmetic(op1);
      if(is_number(op1.type()))
        return;
    }
    else if(final_type0.id()==ID_vector &&
            final_type0==follow(op1.type()))
    {
      return;
    }
    else
    {
      implicit_typecast(op1, op0.type());
      if(is_number(op0.type()))
      {
        expr.type()=type0;
        return;
      }
    }
  }

  err_location(expr);
  str << "assignment `" << statement
      << "' not defined for types `"
      << to_string(o_type0) << "' and `"
      << to_string(o_type1) << "'";

  throw 0;
}

/*******************************************************************\

Function: c_typecheck_baset::make_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::make_constant(exprt &expr)
{
  make_constant_rec(expr);
  simplify(expr, *this);

  if(!expr.is_constant() &&
     expr.id()!=ID_infinity)
  {
    err_location(expr.find_location());
    str << "expected constant expression, but got `"
        << to_string(expr) << "'";
    throw 0;
  }
}

/*******************************************************************\

Function: c_typecheck_baset::make_constant_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::make_constant_index(exprt &expr)
{
  make_constant(expr);
  make_index_type(expr);
  simplify(expr, *this);

  if(!expr.is_constant() &&
     expr.id()!=ID_infinity)
  {
    err_location(expr.find_location());
    throw "conversion to integer failed";
  }
}

/*******************************************************************\

Function: c_typecheck_baset::make_constant_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void c_typecheck_baset::make_constant_rec(exprt &expr)
{
}
