/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <cstdlib>

#include <expr_util.h>
#include <i2string.h>
#include <arith_tools.h>
#include <cprover_prefix.h>
#include <std_types.h>
#include <pointer_offset_size.h>
#include <context.h>
#include <std_expr.h>
#include <std_code.h>
#include <simplify_expr.h>
#include <prefix.h>
#include <string2int.h>

#include <ansi-c/c_types.h>

#include "basic_symex.h"
#include "goto_symex_state.h"

/*******************************************************************\

Function: basic_symext::symex_malloc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static typet c_sizeof_type_rec(const exprt &expr)
{
  const irept &sizeof_type=expr.find(ID_C_c_sizeof_type);

  if(!sizeof_type.is_nil())
  {
    return static_cast<const typet &>(sizeof_type);
  }
  else if(expr.id()==ID_mult)
  {
    forall_operands(it, expr)
    {
      typet t=c_sizeof_type_rec(*it);
      if(t.is_not_nil()) return t;
    }
  }
  
  return nil_typet();
}

void basic_symext::symex_malloc(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=1)
    throw "malloc expected to have one operand";
    
  if(lhs.is_nil())
    return; // ignore

  dynamic_counter++;
  
  exprt size=code.op0();
  typet object_type=nil_typet();
  
  {
    exprt tmp_size=size;
    state.rename(tmp_size, ns); // to allow constant propagation
    
    // special treatment for sizeof(T)*x
    if(tmp_size.id()==ID_mult &&
       tmp_size.operands().size()==2 &&
       tmp_size.op0().find(ID_C_c_sizeof_type).is_not_nil())
    {
      object_type=array_typet(
        c_sizeof_type_rec(tmp_size.op0()),
        tmp_size.op1());      
    }
    else
    {
      typet tmp_type=c_sizeof_type_rec(tmp_size);
      
      if(tmp_type.is_not_nil())
      {
        // Did the size get multiplied?
        mp_integer elem_size=pointer_offset_size(ns, tmp_type);
        mp_integer alloc_size;
        if(elem_size<0 || to_integer(tmp_size, alloc_size))
        {
        }
        else
        {
          if(alloc_size==elem_size)
            object_type=tmp_type;
          else
          {
            mp_integer elements=alloc_size/elem_size;
            
            if(elements*elem_size==alloc_size)
              object_type=array_typet(tmp_type, from_integer(elements, tmp_size.type()));
          }
        }
      }
    }

    if(object_type.is_nil())
      object_type=array_typet(uchar_type(), tmp_size);
      
    // must use renamed size in the above,
    // or it can change!
  }
  
  // value
  symbolt symbol;

  symbol.base_name="dynamic_object"+i2string(dynamic_counter);
  symbol.name="symex_dynamic::"+id2string(symbol.base_name);
  symbol.lvalue=true;
  symbol.type=object_type;
  symbol.type.set("#dynamic", true);
  symbol.mode=ID_C;

  new_context.add(symbol);
  
  address_of_exprt rhs;
  
  if(object_type.id()==ID_array)
  {
    rhs.type()=pointer_typet(symbol.type.subtype());
    index_exprt index_expr(symbol.type.subtype());
    index_expr.array()=symbol_expr(symbol);
    index_expr.index()=gen_zero(index_type());
    rhs.op0()=index_expr;
  }
  else
  {
    rhs.op0()=symbol_expr(symbol);
    rhs.type()=pointer_typet(symbol.type);
  }
  
  if(rhs.type()!=lhs.type())
    rhs.make_typecast(lhs.type());

  state.rename(rhs, ns);
  
  guardt guard;
  symex_assign_rec(state, lhs, nil_exprt(), rhs, guard, VISIBLE);
}

/*******************************************************************\

Function: basic_symext::symex_gcc_builtin_va_arg_next

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt get_symbol(const exprt &src)
{
  if(src.id()==ID_typecast)
    return get_symbol(to_typecast_expr(src).op());
  else if(src.id()==ID_address_of)
  {
    exprt op=to_address_of_expr(src).object();
    if(op.id()==ID_symbol)
      return to_symbol_expr(op).get_identifier();
    else
      return irep_idt();
  }
  else
    return irep_idt();
}

void basic_symext::symex_gcc_builtin_va_arg_next(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  if(code.operands().size()!=1)
    throw "va_arg_next expected to have one operand";
    
  if(lhs.is_nil())
    return; // ignore

  exprt tmp=code.op0();
  state.rename(tmp, ns); // to allow constant propagation
  irep_idt id=get_symbol(tmp);

  exprt rhs=gen_zero(lhs.type());
  
  if(id!=irep_idt())
  {
    id=state.get_original_name(id);
    
    std::string base="symex::va_arg";

    if(has_prefix(id2string(id), base))
      id=base+i2string(
        safe_string2unsigned(
          std::string(id2string(id), base.size(), std::string::npos))+1);
    else
      id=base+"0";

    const symbolt *symbol;
    if(!ns.lookup(id, symbol))
      rhs=symbol_exprt(symbol->name, symbol->type);
  }

  guardt guard;
  symex_assign_rec(state, lhs, nil_exprt(), rhs, guard, VISIBLE);
}

/*******************************************************************\

Function: basic_symext::get_string_argument_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt get_string_argument_rec(const exprt &src)
{
  if(src.id()==ID_typecast)
  {
    assert(src.operands().size()==1);
    return get_string_argument_rec(src.op0());
  }
  else if(src.id()==ID_address_of)
  {
    assert(src.operands().size()==1);
    if(src.op0().id()==ID_index)
    {
      assert(src.op0().operands().size()==2);
      
      if(src.op0().op0().id()==ID_string_constant &&
         src.op0().op1().is_zero())
      {
        const exprt &fmt_str=src.op0().op0();
        return fmt_str.get_string(ID_value);
      }
    }
  }
  
  return "";
}

/*******************************************************************\

Function: basic_symext::get_string_argument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt get_string_argument(const exprt &src, const namespacet &ns)
{
  exprt tmp=src;
  simplify(tmp, ns);
  return get_string_argument_rec(tmp);
}

/*******************************************************************\

Function: basic_symext::symex_printf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_printf(
  statet &state,
  const exprt &lhs,
  const exprt &rhs)
{
  if(rhs.operands().empty())
    throw "printf expected to have at least one operand";

  exprt tmp_rhs=rhs;
  state.rename(tmp_rhs, ns);

  const exprt::operandst &operands=tmp_rhs.operands();
  std::list<exprt> args;

  for(unsigned i=1; i<operands.size(); i++)
    args.push_back(operands[i]);
    
  const irep_idt format_string=
    get_string_argument(operands[0], ns);

  if(format_string!="")
    target.output_fmt(state.guard, state.source, "printf", format_string, args);
}

/*******************************************************************\

Function: basic_symext::symex_input

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_input(
  statet &state,
  const codet &code)
{
  if(code.operands().size()<2)
    throw "input expected to have at least two operands";

  exprt id_arg=code.op0();

  state.rename(id_arg, ns);

  std::list<exprt> args;
  
  for(unsigned i=1; i<code.operands().size(); i++)
  {
    args.push_back(code.operands()[i]);
    state.rename(args.back(), ns);
  }

  const irep_idt input_id=get_string_argument(id_arg, ns);

  target.input(state.guard, state.source, input_id, args);
}

/*******************************************************************\

Function: basic_symext::symex_output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_output(
  statet &state,
  const codet &code)
{
  if(code.operands().size()<2)
    throw "output expected to have at least two operands";

  exprt id_arg=code.op0();

  state.rename(id_arg, ns);

  std::list<exprt> args;
  
  for(unsigned i=1; i<code.operands().size(); i++)
  {
    args.push_back(code.operands()[i]);
    state.rename(args.back(), ns);
  }

  const irep_idt output_id=get_string_argument(id_arg, ns);

  target.output(state.guard, state.source, output_id, args);
}

/*******************************************************************\

Function: basic_symext::symex_cpp_new

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_cpp_new(
  statet &state,
  const exprt &lhs,
  const side_effect_exprt &code)
{
  bool do_array;

  if(code.type().id()!=ID_pointer)
    throw "new expected to return pointer";

  do_array=(code.get(ID_statement)==ID_cpp_new_array);
      
  dynamic_counter++;

  const std::string count_string(i2string(dynamic_counter));

  // value
  symbolt symbol;
  symbol.base_name=
    do_array?"dynamic_"+count_string+"_array":
             "dynamic_"+count_string+"_value";
  symbol.name="symex_dynamic::"+id2string(symbol.base_name);
  symbol.lvalue=true;
  symbol.mode="cpp";
  
  if(do_array)
  {
    symbol.type=array_typet();
    symbol.type.subtype()=code.type().subtype();
    symbol.type.set(ID_size, code.find(ID_size));
  }
  else
    symbol.type=code.type().subtype();

  //symbol.type.set("#active", symbol_expr(active_symbol));
  symbol.type.set("#dynamic", true);
  
  new_context.add(symbol);

  // make symbol expression

  exprt rhs(ID_address_of, pointer_typet());
  rhs.type().subtype()=code.type().subtype();
  
  if(do_array)
  {
    exprt index_expr(ID_index, code.type().subtype());
    index_expr.copy_to_operands(symbol_expr(symbol), gen_zero(index_type()));
    rhs.move_to_operands(index_expr);
  }
  else
    rhs.copy_to_operands(symbol_expr(symbol));
  
  state.rename(rhs, ns);

  guardt guard;
  symex_assign_rec(state, lhs, nil_exprt(), rhs, guard, VISIBLE);
}

/*******************************************************************\

Function: basic_symext::symex_cpp_delete

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_cpp_delete(
  statet &state,
  const codet &code)
{
  //bool do_array=code.get(ID_statement)==ID_cpp_delete_array;
}

/*******************************************************************\

Function: basic_symext::symex_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_trace(
  statet &state,
  const code_function_callt &code)
{
  if(code.arguments().size()<2)
    throw "CBMC_trace expects at least two arguments";

  int debug_thresh=atol(options.get_option("debug-level").c_str());
  
  mp_integer debug_lvl;

  if(to_integer(code.arguments()[0], debug_lvl))
    throw "CBMC_trace expects constant as first argument";
    
  if(code.arguments()[1].id()!="implicit_address_of" ||
     code.arguments()[1].operands().size()!=1 ||
     code.arguments()[1].op0().id()!=ID_string_constant)
    throw "CBMC_trace expects string constant as second argument";
  
  if(mp_integer(debug_thresh)>=debug_lvl)
  {
    std::list<exprt> vars;
    
    irep_idt event=code.arguments()[1].op0().get(ID_value);

    for(unsigned j=2; j<code.arguments().size(); j++)
    {
      exprt var(code.arguments()[j]);
      state.rename(var, ns);
      vars.push_back(var);
    }

    target.output(state.guard, state.source, event, vars);
  }
}

/*******************************************************************\

Function: basic_symext::symex_fkt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_fkt(
  statet &state,
  const code_function_callt &code)
{
  #if 0
  exprt new_fc(ID_function, fc.type());

  new_fc.reserve_operands(fc.operands().size()-1);

  bool first=true;

  Forall_operands(it, fc)
    if(first) first=false; else new_fc.move_to_operands(*it);

  new_fc.set(ID_identifier, fc.op0().get(ID_identifier));

  fc.swap(new_fc);
  #endif
}

/*******************************************************************\

Function: basic_symext::symex_macro

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void basic_symext::symex_macro(
  statet &state,
  const code_function_callt &code)
{
  const irep_idt &identifier=code.op0().get(ID_identifier);

  if(identifier==CPROVER_MACRO_PREFIX "waitfor")
  {
    #if 0
    exprt new_fc("waitfor", fc.type());

    if(fc.operands().size()!=4)
      throw "waitfor expected to have four operands";

    exprt &cycle_var=fc.op1();
    exprt &bound=fc.op2();
    exprt &predicate=fc.op3();

    if(cycle_var.id()!=ID_symbol)
      throw "waitfor expects symbol as first operand but got "+
            cycle_var.id();

    exprt new_cycle_var(cycle_var);
    new_cycle_var.id("waitfor_symbol");
    new_cycle_var.copy_to_operands(bound);

    replace_expr(cycle_var, new_cycle_var, predicate);

    new_fc.operands().resize(4);
    new_fc.op0().swap(cycle_var);
    new_fc.op1().swap(new_cycle_var);
    new_fc.op2().swap(bound);
    new_fc.op3().swap(predicate);

    fc.swap(new_fc);
    #endif
  }
  else
    throw "unknown macro: "+id2string(identifier);
}
