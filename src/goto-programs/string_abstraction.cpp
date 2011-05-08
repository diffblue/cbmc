/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string.h>

#include <std_expr.h>
#include <std_code.h>
#include <expr_util.h>
#include <message_stream.h>
#include <arith_tools.h>
#include <i2string.h>

#include <ansi-c/c_types.h>

#include "pointer_arithmetic.h"
#include "string_abstraction.h"

/*******************************************************************\

Function: string_abstraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstraction(
  contextt &context,
  message_handlert &message_handler,
  goto_programt &dest)
{
  string_abstractiont string_abstraction(context, message_handler);
  string_abstraction(dest);
}

/*******************************************************************\

Function: string_abstraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstraction(
  contextt &context,
  message_handlert &message_handler,
  goto_functionst &dest)
{
  string_abstractiont string_abstraction(context, message_handler);
  string_abstraction(dest);
}

/*******************************************************************\

Function: string_abstractiont::string_abstractiont

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

string_abstractiont::string_abstractiont(
  contextt &_context,
  message_handlert &_message_handler):
  message_streamt(_message_handler),
  context(_context),
  ns(_context)
{
  struct_typet s;

  s.components().resize(3);

  s.components()[0].set_name("is_zero");
  s.components()[0].set_pretty_name("is_zero");
  s.components()[0].type()=build_type(IS_ZERO);

  s.components()[1].set_name("length");
  s.components()[1].set_pretty_name("length");
  s.components()[1].type()=build_type(LENGTH);

  s.components()[2].set_name("size");
  s.components()[2].set_pretty_name("size");
  s.components()[2].type()=build_type(SIZE);

  string_struct=s;
}

/*******************************************************************\

Function: string_abstractiont::member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::member(const exprt &a, whatt what)
{
  if(a.is_nil()) return a;
  
  member_exprt result;
  result.type()=build_type(what);
  result.struct_op()=a;

  switch(what)
  {
  case IS_ZERO: result.set_component_name("is_zero"); break;
  case SIZE: result.set_component_name("size"); break;
  case LENGTH: result.set_component_name("length"); break;
  default: assert(false);
  }

  return result;
}

/*******************************************************************\

Function: string_abstractiont::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::operator()(goto_functionst &dest)
{
  for(goto_functionst::function_mapt::iterator
      it=dest.function_map.begin();
      it!=dest.function_map.end();
      it++)
    abstract(it->second.body);

  // do we have a main?
  goto_functionst::function_mapt::iterator
    m_it=dest.function_map.find(dest.main_id());

  if(m_it!=dest.function_map.end())
  {
    goto_programt &main=m_it->second.body;

    // do initialization
    initialization.destructive_append(main);
    main.swap(initialization);
    initialization.clear();
  }
}

/*******************************************************************\

Function: string_abstractiont::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::operator()(goto_programt &dest)
{
  abstract(dest);

  // do initialization
  initialization.destructive_append(dest);
  dest.swap(initialization);
  initialization.clear();
}

/*******************************************************************\

Function: string_abstractiont::abstract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::abstract(goto_programt &dest)
{
  locals.clear();

  Forall_goto_program_instructions(it, dest)
    abstract(dest, it);

  // go over it again for the newly added locals
  if(!locals.empty())
  {
    Forall_goto_program_instructions(it, dest)
    {
      // do declaration/initializations of those locals
      if(it->is_decl())
      {
        assert(it->code.get(ID_statement)==ID_decl);
        assert(it->code.operands().size()==1);
        assert(it->code.op0().id()==ID_symbol);

        const irep_idt &identifier=
          to_symbol_expr(it->code.op0()).get_identifier();

        localst::const_iterator l_it=locals.find(identifier);
        if(l_it==locals.end()) continue;
        
        const symbolt &symbol=ns.lookup(l_it->second);
        
        // do declaration
        goto_programt tmp;

        goto_programt::targett decl1=tmp.add_instruction();
        decl1->make_decl();
        decl1->code=code_declt(symbol_expr(symbol));
        decl1->location=it->location;

        if(symbol.value.is_not_nil())
        {
          // initialization
          goto_programt::targett assignment1=tmp.add_instruction(ASSIGN);
          assignment1->code=code_assignt(symbol_expr(symbol), symbol.value);
          assignment1->location=it->location;
        }

        goto_programt::targett it_next=it;
        it_next++;

        dest.destructive_insert(it_next, tmp);
      }
    }
  }

  locals.clear();
}

/*******************************************************************\

Function: string_abstractiont::abstract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::abstract(
  goto_programt &dest,
  goto_programt::targett it)
{
  switch(it->type)
  {
  case ASSIGN:
    abstract_assign(dest, it);
    break;
    
  case GOTO:
  case ASSERT:
  case ASSUME:
    if(has_string_macros(it->guard))
      replace_string_macros(it->guard, false, it->location);
    break;
    
  case FUNCTION_CALL:
    abstract_function_call(dest, it);
    break;
    
  case RETURN:
    if(it->code.operands().size()!=0)
      replace_string_macros(it->code.op0(), false, it->location);
    break;
    
  default:;  
  }
}

/*******************************************************************\

Function: string_abstractiont::has_string_macros

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool string_abstractiont::has_string_macros(const exprt &expr)
{
  if(expr.id()=="is_zero_string" ||
     expr.id()=="zero_string_length" ||
     expr.id()=="buffer_size")
    return true;

  forall_operands(it, expr)
    if(has_string_macros(*it))
      return true;

  return false;
}

/*******************************************************************\

Function: string_abstractiont::replace_string_macros

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::replace_string_macros(
  exprt &expr,
  bool lhs,
  const locationt &location)
{
  if(expr.id()=="is_zero_string")
  {
    assert(expr.operands().size()==1);
    exprt tmp=is_zero_string(expr.op0(), lhs, location);
    expr.swap(tmp);
  }
  else if(expr.id()=="zero_string_length")
  {
    assert(expr.operands().size()==1);
    exprt tmp=zero_string_length(expr.op0(), lhs, location);
    expr.swap(tmp);
  }
  else if(expr.id()=="buffer_size")
  {
    assert(expr.operands().size()==1);
    exprt tmp=buffer_size(expr.op0(), location);
    expr.swap(tmp);
  }
  else
    Forall_operands(it, expr)
      replace_string_macros(*it, lhs, location);
}

/*******************************************************************\

Function: string_abstractiont::build_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet string_abstractiont::build_type(whatt what)
{
  typet type;

  switch(what)
  {
  case IS_ZERO: type=bool_typet(); break;
  case LENGTH:  type=uint_type(); break;
  case SIZE:    type=uint_type(); break;
  default: assert(false);
  }

  return type;
}

/*******************************************************************\

Function: string_abstractiont::build_unknown

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::build_unknown(whatt what, bool write)
{
  typet type=build_type(what);

  if(write)
    return exprt("NULL-object", type);

  exprt result;

  switch(what)
  {
  case IS_ZERO:
    result=false_exprt();
    break;

  case LENGTH:
  case SIZE:
    result=exprt(ID_sideeffect, type);
    result.set(ID_statement, ID_nondet);
    break;

  default: assert(false);
  }

  return result;
}

/*******************************************************************\

Function: string_abstractiont::build_unknown

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::build_unknown(bool write)
{
  typet type=pointer_typet();
  type.subtype()=string_struct;

  if(write)
    return exprt("NULL-object", type);

  exprt result=exprt("constant", type);
  result.set(ID_value, ID_NULL);

  return result;
}

/*******************************************************************\

Function: string_abstractiont::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::build(
  const exprt &pointer,
  whatt what,
  bool write,
  const locationt &location)
{
  // take care of pointer typecasts now
  if(pointer.id()==ID_typecast)
  {
    // cast from another pointer type?
    assert(pointer.operands().size()==1);
    if(pointer.op0().type().id()!=ID_pointer)
      return build_unknown(what, write);

    // recursive call
    return build(pointer.op0(), what, write, location);
  }

  exprt str_ptr=build(pointer, write);

  exprt deref=dereference_exprt(string_struct);
  deref.op0()=str_ptr;
  deref.location()=location;

  exprt result=member(deref, what);

  if(what==LENGTH || what==SIZE)
  {
    // adjust for offset
    exprt pointer_offset(ID_pointer_offset, uint_type());
    pointer_offset.copy_to_operands(pointer);
    result=sub(result, pointer_offset);
  }

  return result;
}

/*******************************************************************\

Function: string_abstractiont::build_symbol_ptr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::build_symbol_ptr(const exprt &object)
{
  std::string suffix="#str";
  const exprt *p=&object;

  while(p->id()==ID_member)
  {
    suffix="#"+p->get_string(ID_component_name)+suffix;
    assert(p->operands().size()==1);
    p=&(p->op0());
  }

  if(p->id()!=ID_symbol)
    return static_cast<const exprt &>(get_nil_irep());

  const symbol_exprt &expr_symbol=to_symbol_expr(*p);

  const symbolt &symbol=ns.lookup(expr_symbol.get_identifier());
  irep_idt identifier=id2string(symbol.name)+suffix;

  typet type=pointer_typet();
  type.subtype()=string_struct;

  if(context.symbols.find(identifier)==
     context.symbols.end())
  {
    symbolt new_symbol;
    new_symbol.name=identifier;
    new_symbol.mode=symbol.mode;
    new_symbol.type=type;
    new_symbol.is_statevar=true;
    new_symbol.lvalue=true;
    new_symbol.static_lifetime=symbol.static_lifetime;
    new_symbol.thread_local=symbol.thread_local;
    new_symbol.pretty_name=id2string(symbol.pretty_name)+suffix;
    new_symbol.module=symbol.module;
    new_symbol.base_name=id2string(symbol.base_name)+suffix;

    context.move(new_symbol);
  }

  const symbolt &str_symbol=ns.lookup(identifier);

  if(!str_symbol.static_lifetime)
    locals[symbol.name]=str_symbol.name;

  return symbol_expr(str_symbol);
}

/*******************************************************************\

Function: string_abstractiont::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::build(const exprt &pointer, bool write)
{
  // take care of typecasts
  if(pointer.id()==ID_typecast)
  {
    // cast from another pointer type?
    assert(pointer.operands().size()==1);
    if(pointer.op0().type().id()!=ID_pointer)
      return build_unknown(write);

    // recursive call
    return build(pointer.op0(), write);
  }

  // take care of if
  if(pointer.id()==ID_if)
  {
    exprt result=if_exprt();

    // recursive call
    result.op0()=pointer.op0();
    result.op1()=build(pointer.op1(), write);
    result.op2()=build(pointer.op2(), write);
    result.type()=result.op1().type();
    return result;
  }

  pointer_arithmetict ptr(pointer);

  if(ptr.pointer.id()==ID_address_of)
  {
    if(write)
      build_unknown(write);

    assert(ptr.pointer.operands().size()==1);

    if(ptr.pointer.op0().id()==ID_index)
    {
      assert(ptr.pointer.op0().operands().size()==2);

      const exprt &o=ptr.pointer.op0().op0();

      if(o.id()==ID_string_constant)
      {
        exprt symbol=build_symbol_constant(o.get(ID_value));

        if(symbol.is_nil())
          return build_unknown(write);

        exprt address_of(ID_address_of, pointer_typet());
        address_of.type().subtype()=string_struct;
        address_of.copy_to_operands(symbol);

        return address_of;
      }

      exprt symbol=build_symbol_buffer(o);

      if(symbol.is_nil())
        return build_unknown(write);

      exprt address_of(ID_address_of, pointer_typet());
      address_of.type().subtype()=string_struct;
      address_of.copy_to_operands(symbol);

      return address_of;
    }
  }
  else
  {
    exprt result=build_symbol_ptr(ptr.pointer);

    if(result.is_nil())
      return build_unknown(write);

    return result;
  }

  return build_unknown(write);
}

/*******************************************************************\

Function: string_abstractiont::build_symbol_buffer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::build_symbol_buffer(const exprt &object)
{
  // first of all, it must be a buffer
  const typet &obj_t=ns.follow(object.type());

  if(obj_t.id()!=ID_array)  
    return static_cast<const exprt &>(get_nil_irep());

  const array_typet &obj_array_type=to_array_type(obj_t);

  // we do buffers, arrays of buffers, and a buffer in a struct

  if(object.id()==ID_index)
  {
    assert(object.operands().size()==2);

    const typet &t=ns.follow(object.op0().type());

    if(object.op0().id()!=ID_symbol ||
       t.id()!=ID_array)
      return static_cast<const exprt &>(get_nil_irep());

    const symbol_exprt &expr_symbol=to_symbol_expr(object.op0());

    const symbolt &symbol=ns.lookup(expr_symbol.get_identifier());
    std::string suffix="#str_array";
    irep_idt identifier=id2string(symbol.name)+suffix;

    if(context.symbols.find(identifier)==
       context.symbols.end())
    {
      array_typet new_type;
      new_type.size()=to_array_type(t).size();
      new_type.subtype()=string_struct;

      symbolt new_symbol;
      new_symbol.name=identifier;
      new_symbol.mode=symbol.mode;
      new_symbol.type=new_type;
      new_symbol.is_statevar=true;
      new_symbol.lvalue=true;
      new_symbol.static_lifetime=symbol.static_lifetime;
      new_symbol.thread_local=symbol.thread_local;
      new_symbol.pretty_name=id2string(symbol.pretty_name)+suffix;
      new_symbol.module=symbol.module;
      new_symbol.base_name=id2string(symbol.base_name)+suffix;
      new_symbol.value.make_nil();

      {
        exprt struct_expr=exprt(ID_struct, string_struct);
        struct_expr.operands().resize(3);
        struct_expr.op0()=false_exprt();
        struct_expr.op1()=obj_array_type.size();
        make_type(struct_expr.op1(), build_type(SIZE));
        struct_expr.op2()=struct_expr.op1();

        exprt value=exprt(ID_array_of, new_type);
        value.copy_to_operands(struct_expr);
        
        new_symbol.value=value;
      }

      if(symbol.static_lifetime)
      {
        // initialization
        goto_programt::targett assignment1=
          initialization.add_instruction(ASSIGN);
        assignment1->code=code_assignt(symbol_expr(new_symbol), new_symbol.value);
      }
      else
      {
        // declaration
        
      }

      context.move(new_symbol);
    }

    const symbolt &str_array_symbol=ns.lookup(identifier);

    if(!str_array_symbol.static_lifetime)
      locals[symbol.name]=str_array_symbol.name;

    index_exprt result;
    result.array()=symbol_expr(str_array_symbol);
    result.index()=object.op1();
    result.type()=string_struct;

    return result;
  }

  // possibly walk over some members

  std::string suffix="#str";
  const exprt *p=&object;

  while(p->id()==ID_member)
  {
    suffix="#"+p->get_string(ID_component_name)+suffix;
    assert(p->operands().size()==1);
    p=&(p->op0());
  }

  if(p->id()!=ID_symbol)
    return static_cast<const exprt &>(get_nil_irep());

  const symbol_exprt &expr_symbol=to_symbol_expr(*p);

  const symbolt &symbol=ns.lookup(expr_symbol.get_identifier());
  irep_idt identifier=id2string(symbol.name)+suffix;

  if(context.symbols.find(identifier)==
     context.symbols.end())
  {
    symbolt new_symbol;
    new_symbol.name=identifier;
    new_symbol.mode=symbol.mode;
    new_symbol.type=string_struct;
    new_symbol.is_statevar=true;
    new_symbol.lvalue=true;
    new_symbol.static_lifetime=symbol.static_lifetime;
    new_symbol.thread_local=symbol.thread_local;
    new_symbol.pretty_name=id2string(symbol.pretty_name)+suffix;
    new_symbol.module=symbol.module;
    new_symbol.base_name=id2string(symbol.base_name)+suffix;

    {    
      exprt value=exprt(ID_struct, string_struct);
      value.operands().resize(3);
      value.op0()=false_exprt();
      value.op1()=obj_array_type.size();
      make_type(value.op1(), build_type(SIZE));
      value.op2()=value.op1();
      
      new_symbol.value=value;
    }

    if(symbol.static_lifetime)
    {
      // initialization
      goto_programt::targett assignment1=initialization.add_instruction(ASSIGN);
      assignment1->code=code_assignt(symbol_expr(new_symbol), new_symbol.value);
    }
    else
    {
      // declaration
    }

    context.move(new_symbol);
  }

  const symbolt &str_symbol=ns.lookup(identifier);

  if(!str_symbol.static_lifetime)
    locals[symbol.name]=str_symbol.name;

  return symbol_expr(str_symbol);
}

/*******************************************************************\

Function: string_abstractiont::build_symbol_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::build_symbol_constant(const irep_idt &str)
{
  unsigned l=strlen(str.c_str());
  irep_idt base="string_constant_str_"+i2string(l);
  irep_idt identifier="string_abstraction::"+id2string(base);

  if(context.symbols.find(identifier)==
     context.symbols.end())
  {
    symbolt new_symbol;
    new_symbol.name=identifier;
    new_symbol.mode="C";
    new_symbol.type=string_struct;
    new_symbol.is_statevar=true;
    new_symbol.lvalue=true;
    new_symbol.static_lifetime=true;
    new_symbol.pretty_name=base;
    new_symbol.base_name=base;

    {
      exprt value=exprt(ID_struct, string_struct);
      value.operands().resize(3);

      value.op0()=true_exprt();
      value.op1()=from_integer(l, build_type(LENGTH));
      value.op2()=from_integer(l+1, build_type(SIZE));

      // initialization
      goto_programt::targett assignment1=initialization.add_instruction(ASSIGN);
      assignment1->code=code_assignt(symbol_expr(new_symbol), value);
    }

    context.move(new_symbol);
  }

  symbol_exprt symbol_expr;
  symbol_expr.type()=string_struct;
  symbol_expr.set_identifier(identifier);

  return symbol_expr;
}

/*******************************************************************\

Function: string_abstractiont::is_zero_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::is_zero_string(
  const exprt &object,
  bool write,
  const locationt &location)
{
  return build(object, IS_ZERO, write, location);
}

/*******************************************************************\

Function: string_abstractiont::zero_string_length

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::zero_string_length(
  const exprt &object,
  bool write,
  const locationt &location)
{
  return build(object, LENGTH, write, location);
}

/*******************************************************************\

Function: string_abstractiont::buffer_size

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt string_abstractiont::buffer_size(
  const exprt &object,
  const locationt &location)
{
  return build(object, SIZE, false, location);
}

/*******************************************************************\

Function: string_abstractiont::move_lhs_arithmetic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::move_lhs_arithmetic(exprt &lhs, exprt &rhs)
{
  if(lhs.id()=="-")
  {
    // move op1 to rhs
    exprt rest=lhs.op0();
    exprt sum=exprt("+", lhs.type());
    sum.copy_to_operands(rhs, lhs.op1());
    // overwrite
    rhs=sum;
    lhs=rest;
  }
}

/*******************************************************************\

Function: string_abstractiont::abstract_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::abstract_assign(
  goto_programt &dest,
  goto_programt::targett target)
{
  code_assignt &assign=to_code_assign(target->code);

  exprt &lhs=assign.lhs();
  exprt &rhs=assign.rhs();

  if(has_string_macros(lhs))
  {
    replace_string_macros(lhs, true, target->location);
    move_lhs_arithmetic(lhs, rhs);
  }

  if(has_string_macros(rhs))
    replace_string_macros(rhs, false, target->location);

  if(lhs.type().id()==ID_pointer)
    abstract_pointer_assign(dest, target);
  else if(is_char_type(lhs.type()))
    abstract_char_assign(dest, target);
}

/*******************************************************************\

Function: string_abstractiont::abstract_pointer_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::abstract_pointer_assign(
  goto_programt &dest,
  goto_programt::targett target)
{
  code_assignt &assign=to_code_assign(target->code);

  exprt &lhs=assign.lhs();
  exprt rhs=assign.rhs();
  exprt *rhsp=&(assign.rhs());

  while(rhsp->id()==ID_typecast)
    rhsp=&(rhsp->op0());
  
  // we only care about char pointers for now
  if(!is_char_type(rhsp->type().subtype()))
    return;

  // assign length and is_zero as well

  goto_programt tmp;

  goto_programt::targett assignment=tmp.add_instruction(ASSIGN);
  assignment->code=code_assignt(build(lhs, true), build(rhs, false));
  assignment->location=target->location;

  target++;
  dest.destructive_insert(target, tmp);
}

/*******************************************************************\

Function: string_abstractiont::abstract_char_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::abstract_char_assign(
  goto_programt &dest,
  goto_programt::targett target)
{
  code_assignt &assign=to_code_assign(target->code);

  exprt &lhs=assign.lhs();
  exprt &rhs=assign.rhs();

  // we only care if the constant zero is assigned
  if(!rhs.is_zero())
    return;

  if(lhs.id()==ID_index)
  {
    assert(lhs.operands().size()==2);

    goto_programt tmp;

    const exprt symbol_buffer=build_symbol_buffer(lhs.op0());

    const exprt i1=member(symbol_buffer, IS_ZERO);
    if(i1.is_not_nil())
    {
      goto_programt::targett assignment1=tmp.add_instruction(ASSIGN);
      assignment1->code=code_assignt(i1, true_exprt());
      assignment1->code.location()=target->location;
      assignment1->location=target->location;
    }

    const exprt i2=member(symbol_buffer, LENGTH);
    if(i2.is_not_nil())
    {
      exprt new_length=lhs.op1();
      make_type(new_length, i2.type());

      if_exprt min_expr;
      min_expr.cond()=binary_relation_exprt(new_length, "<", i2);
      min_expr.true_case()=new_length;
      min_expr.false_case()=i2;
      min_expr.type()=i2.type();

      goto_programt::targett assignment2=tmp.add_instruction(ASSIGN);
      assignment2->code=code_assignt(i2, min_expr);
      assignment2->code.location()=target->location;
      assignment2->location=target->location;

      move_lhs_arithmetic(
       assignment2->code.op0(),
       assignment2->code.op1());
    }

    target++;
    dest.destructive_insert(target, tmp);
  }
  else if(lhs.id()==ID_dereference)
  {
    assert(lhs.operands().size()==1);

  }
}

/*******************************************************************\

Function: string_abstractiont::abstract_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_abstractiont::abstract_function_call(
  goto_programt &dest,
  goto_programt::targett target)
{
  const code_function_callt &call=to_code_function_call(target->code);
  const code_function_callt::argumentst &arguments=call.arguments();
  
  contextt::symbolst::const_iterator f_it = 
    context.symbols.find(call.function().get(ID_identifier));

  if(f_it==context.symbols.end())
    throw "invalid function call";
  
  const code_typet &fnc_type = 
    static_cast<const code_typet &>(f_it->second.type);
  const code_typet::argumentst &argument_types=fnc_type.arguments();
  
  exprt::operandst::const_iterator it1=arguments.begin();

  for(code_typet::argumentst::const_iterator it2=argument_types.begin();
      it2!=argument_types.end();
      it2++)
  {
    if(it1==arguments.end())
    {
      err_location(target->location);
      throw "function call: not enough arguments";
    }
    
    const exprt &argument=static_cast<const exprt &>(*it2);
    
    const exprt actual(*it1);
    
    const exprt *tcfree = &actual;
    while(tcfree->id()==ID_typecast)
      tcfree=&tcfree->op0();
    
    if(tcfree->type().id()==ID_pointer &&
       is_char_type(tcfree->type().subtype()))
    {
      const irep_idt &identifier=argument.get("#identifier");
      
      if(identifier=="") continue; // just forget it
      
      goto_programt tmp;
      
      goto_programt::targett assignment=tmp.add_instruction(ASSIGN);
      assignment->code=code_assignt(
                         build(symbol_exprt(identifier, argument.type()), true), 
                         build(actual, false));
      assignment->location=target->location;
      assignment->function=call.function().get(ID_identifier);

      // inserts _before_ the call
      dest.destructive_insert(target, tmp);
    }
    
    it1++;
  }
}
