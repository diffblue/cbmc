/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_expr.h>
#include <std_code.h>
#include <expr_util.h>
#include <message_stream.h>
#include <arith_tools.h>
#include <config.h>
#include <bitvector.h>

#include <goto-programs/format_strings.h>
#include <ansi-c/c_types.h>

#include "string_instrumentation.h"

/*******************************************************************\

   Class: string_instrumentationt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class string_instrumentationt:public message_streamt
{
public:
  string_instrumentationt(
    contextt &_context,
    message_handlert &_message_handler):
    message_streamt(_message_handler),
    context(_context),
    ns(_context)
  {
  }
  
  void operator()(goto_programt &dest);
  void operator()(goto_functionst &dest);

  exprt is_zero_string(
    const exprt &what,
    bool write=false)
  {
    exprt result=predicate_exprt("is_zero_string");
    result.copy_to_operands(what);
    result.set("lhs", write);
    return result;
  }

  exprt zero_string_length(
    const exprt &what,
    bool write=false)
  {
    exprt result("zero_string_length", uint_type());
    result.copy_to_operands(what);
    result.set("lhs", write);
    return result;
  }

  exprt buffer_size(const exprt &what)
  {
    exprt result("buffer_size", uint_type());
    result.copy_to_operands(what);
    return result;
  }

protected:
  contextt &context;
  namespacet ns;

  void make_type(exprt &dest, const typet &type)
  {
    if(ns.follow(dest.type())!=ns.follow(type))
      dest.make_typecast(type);
  }

  void instrument(goto_programt &dest, goto_programt::targett it);
  void do_function_call(goto_programt &dest, goto_programt::targett it);

  // strings
  void do_sprintf (goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  void do_snprintf(goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  void do_strcat  (goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  void do_strncmp (goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  void do_strchr  (goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  void do_strrchr (goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  void do_strstr  (goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  void do_strtok  (goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  void do_strerror(goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  void do_fscanf  (goto_programt &dest, goto_programt::targett it, code_function_callt &call);
  
  void do_format_string_read(
    goto_programt &dest,
    goto_programt::const_targett target,
    const code_function_callt::argumentst &arguments,
    unsigned format_string_inx,
    unsigned argument_start_inx,
    const std::string &function_name);
  
  void do_format_string_write(
    goto_programt &dest,
    goto_programt::const_targett target,
    const code_function_callt::argumentst &arguments,
    unsigned format_string_inx,
    unsigned argument_start_inx,
    const std::string &function_name);
  
  bool is_string_type(const typet &t) const
  {
    return ((t.id()==ID_pointer || t.id()==ID_array) && 
            (t.subtype().id()==ID_signedbv || t.subtype().id()==ID_unsignedbv) &&
            (to_bitvector_type(t.subtype()).get_width()==config.ansi_c.char_width));
  }
  
  void invalidate_buffer(
    goto_programt &dest,
    goto_programt::const_targett target,
    const exprt &buffer,
    const typet &buf_type,
    const mp_integer &limit);
};

/*******************************************************************\

Function: string_instrumentation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentation(
  contextt &context,
  message_handlert &message_handler,
  goto_programt &dest)
{
  string_instrumentationt string_instrumentation(context, message_handler);
  string_instrumentation(dest);
}

/*******************************************************************\

Function: string_instrumentation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentation(
  contextt &context,
  message_handlert &message_handler,
  goto_functionst &dest)
{
  string_instrumentationt string_instrumentation(context, message_handler);
  string_instrumentation(dest);
}

/*******************************************************************\

Function: string_instrumentationt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::operator()(goto_functionst &dest)
{
  for(goto_functionst::function_mapt::iterator
      it=dest.function_map.begin();
      it!=dest.function_map.end();
      it++)
  {
    (*this)(it->second.body);
  }
}

/*******************************************************************\

Function: string_instrumentationt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::operator()(goto_programt &dest)
{
  Forall_goto_program_instructions(it, dest)
    instrument(dest, it);
}

/*******************************************************************\

Function: string_instrumentationt::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::instrument(
  goto_programt &dest,
  goto_programt::targett it)
{
  switch(it->type)
  {
  case ASSIGN:
    break;
    
  case FUNCTION_CALL:
    do_function_call(dest, it);
    break;
    
  default:;  
  }
}

/*******************************************************************\

Function: string_instrumentationt::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_function_call(
  goto_programt &dest,
  goto_programt::targett target)
{
  code_function_callt &call=
    to_code_function_call(target->code);
  exprt &function=call.function();
  //const exprt &lhs=call.lhs();
  
  if(function.id()=="symbol")
  {
    const irep_idt &identifier=
      to_symbol_expr(function).get_identifier();

    if(identifier=="c::strcoll")
    {
    }
    else if(identifier=="c::strncmp")
      do_strncmp(dest, target, call);
    else if(identifier=="c::strxfrm")
    {
    }
    else if(identifier=="c::strchr")
      do_strchr(dest, target, call);
    else if(identifier=="c::strcspn")
    {
    }
    else if(identifier=="c::strpbrk")
    {
    }
    else if(identifier=="c::strrchr")
      do_strrchr(dest, target, call);
    else if(identifier=="c::strspn")
    {
    }
    else if(identifier=="c::strerror")
      do_strerror(dest, target, call);
    else if(identifier=="c::strstr")
      do_strstr(dest, target, call);
    else if(identifier=="c::strtok")
      do_strtok(dest, target, call);
    else if(identifier=="c::sprintf")
      do_sprintf(dest, target, call);
    else if(identifier=="c::snprintf")
      do_snprintf(dest, target, call);
    else if(identifier=="c::fscanf")
      do_fscanf(dest, target, call);
    
    dest.update();
  }
}

/*******************************************************************\

Function: string_instrumentationt::do_sprintf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_sprintf(
  goto_programt &dest,
  goto_programt::targett target,
  code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();
    
  if(arguments.size()<2)
  {
    err_location(target->location);
    throw "sprintf expected to have two or more arguments";
  }
  
  goto_programt tmp;
  
  goto_programt::targett assertion=tmp.add_instruction();  
  assertion->location=target->location;
  assertion->location.set("property", "string");  
  assertion->location.set("comment", "sprintf buffer overflow");
  
  // in the abstract model, we have to report a 
  // (possibly false) positive here
  assertion->make_assertion(false_exprt());
  
  do_format_string_read(tmp, target, arguments, 1, 2, "sprintf");
  
  if(call.lhs().is_not_nil())
  {
    goto_programt::targett return_assignment=tmp.add_instruction(ASSIGN);
    return_assignment->location=target->location;
    
    exprt rhs=side_effect_expr_nondett(call.lhs().type());
    rhs.location()=target->location;
      
    return_assignment->code=code_assignt(call.lhs(), rhs);
  }
  
  target->make_skip();
  dest.insert_before_swap(target, tmp);
}

/*******************************************************************\

Function: string_instrumentationt::do_snprintf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_snprintf(
  goto_programt &dest,
  goto_programt::targett target,
  code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();
  
  if(arguments.size()<3)
  {
    err_location(target->location);
    throw "snprintf expected to have three or more arguments";
  }
  
  goto_programt tmp;
  
  goto_programt::targett assertion=tmp.add_instruction();  
  assertion->location=target->location;
  assertion->location.set("property", "string");  
  assertion->location.set("comment", "snprintf buffer overflow");
  
  exprt bufsize = buffer_size(arguments[0]);
  assertion->make_assertion(binary_relation_exprt(bufsize, ">=", arguments[1]));
  
  do_format_string_read(tmp, target, arguments, 2, 3, "snprintf");
  
  if(call.lhs().is_not_nil())
  {
    goto_programt::targett return_assignment=tmp.add_instruction(ASSIGN);
    return_assignment->location=target->location;
      
    exprt rhs=side_effect_expr_nondett(call.lhs().type());
    rhs.location()=target->location;
      
    return_assignment->code=code_assignt(call.lhs(), rhs);
  }
  
  target->make_skip();
  dest.insert_before_swap(target, tmp);
}

/*******************************************************************\

Function: string_instrumentationt::do_fscanf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_fscanf(
  goto_programt &dest,
  goto_programt::targett target,
  code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();
  
  if(arguments.size()<2)
  {
    err_location(target->location);
    throw "fscanf expected to have two or more arguments";
  }
  
  goto_programt tmp;
  
  do_format_string_write(tmp, target, arguments, 1, 2, "fscanf");
  
  if(call.lhs().is_not_nil())
  {
    goto_programt::targett return_assignment=tmp.add_instruction(ASSIGN);
    return_assignment->location=target->location;
      
    exprt rhs=side_effect_expr_nondett(call.lhs().type());
    rhs.location()=target->location;
      
    return_assignment->code=code_assignt(call.lhs(), rhs);
  }
  
  target->make_skip();
  dest.insert_before_swap(target, tmp);
}

/*******************************************************************\

Function: string_instrumentationt::do_format_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_format_string_read(
  goto_programt &dest,
  goto_programt::const_targett target,
  const code_function_callt::argumentst &arguments,
  unsigned format_string_inx,
  unsigned argument_start_inx,
  const std::string &function_name)
{
  const exprt &format_arg = arguments[format_string_inx];
  
  if(format_arg.id()=="address_of" &&
     format_arg.op0().id()=="index" &&
     format_arg.op0().op0().id()==ID_string_constant)
  {
    format_token_listt token_list;
    parse_format_string(format_arg.op0().op0(), token_list);
    
    unsigned args=0;
    
    for(format_token_listt::const_iterator it=token_list.begin();
        it!=token_list.end();
        it++)
    {
      if(it->type==format_tokent::STRING)
      {
        const exprt &arg = arguments[argument_start_inx+args];
        const typet &arg_type = ns.follow(arg.type());
        
        if(arg.id()!=ID_string_constant) // we don't need to check constants
        {
          goto_programt::targett assertion=dest.add_instruction();
          assertion->location=target->location;
          assertion->location.set("property", "string");
          std::string comment("zero-termination of string argument of ");
          comment += function_name;
          assertion->location.set("comment", comment);
          
          exprt temp(arg);
          
          if(arg_type.id()!="pointer")
          {
            index_exprt index;
            index.array()=temp;
            index.index()=gen_zero(uint_type());
            index.type()=arg_type.subtype();            
            temp=address_of_exprt(index);            
          }
          
          assertion->make_assertion(is_zero_string(temp));
        }
      }
      
      if(it->type!=format_tokent::TEXT && 
         it->type!=format_tokent::UNKNOWN) args++;
      
      if(find(it->flags.begin(), it->flags.end(), format_tokent::ASTERISK)!=
         it->flags.end())
        args++; // just eat the additional argument          
    }
  }
  else // non-const format string
  {
    goto_programt::targett format_ass=dest.add_instruction();
    format_ass->make_assertion(is_zero_string(arguments[1]));
    format_ass->location=target->location;
    format_ass->location.set("property", "string");
    std::string comment("zero-termination of format string of ");
    comment += function_name;
    format_ass->location.set("comment", comment);
    
    for(unsigned i=2; i<arguments.size(); i++)
    {
      const exprt &arg = arguments[i];
      const typet &arg_type=ns.follow(arguments[i].type());
      
      if(arguments[i].id()!=ID_string_constant &&
         is_string_type(arg_type))
      {
        goto_programt::targett assertion=dest.add_instruction();        
        assertion->location=target->location;
        assertion->location.set("property", "string");
        std::string comment("zero-termination of string argument of ");
        comment += function_name;
        assertion->location.set("comment", comment);
        
        exprt temp(arg);
                  
        if(arg_type.id()!="pointer")
        {
          index_exprt index;
          index.array()=temp;
          index.index()=gen_zero(uint_type());
          index.type()=arg_type.subtype();            
          temp=address_of_exprt(index);            
        }
        
        assertion->make_assertion(is_zero_string(temp));
      }
    }
  }
}

/*******************************************************************\

Function: string_instrumentationt::do_format_string_write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_format_string_write(
  goto_programt &dest,
  goto_programt::const_targett target,
  const code_function_callt::argumentst &arguments,
  unsigned format_string_inx,
  unsigned argument_start_inx,
  const std::string &function_name)
{
  const exprt &format_arg = arguments[format_string_inx];
    
  if(format_arg.id()=="address_of" &&
     format_arg.op0().id()=="index" &&
     format_arg.op0().op0().id()==ID_string_constant) // constant format
  {
    format_token_listt token_list;
    parse_format_string(format_arg.op0().op0(), token_list);
    
    unsigned args=0;
    
    for(format_token_listt::const_iterator it=token_list.begin();
        it!=token_list.end();
        it++)
    {
      if(find(it->flags.begin(), it->flags.end(), format_tokent::ASTERISK)!=
         it->flags.end()) 
        continue; // asterisk means `ignore this'
      
      switch(it->type)
      {
        case format_tokent::STRING:
        {
            
          const exprt &argument=arguments[argument_start_inx+args];
          const typet &arg_type=ns.follow(argument.type());
          
          goto_programt::targett assertion=dest.add_instruction();
          assertion->location=target->location;
          assertion->location.set("property", "string");
          std::string comment("format string buffer overflow in ");
          comment += function_name;
          assertion->location.set("comment", comment);
          
          if(it->field_width!=0)
          {
            exprt fwidth = from_integer(it->field_width, uint_type());
            exprt fw_1("+", uint_type());
            exprt one = gen_one(uint_type());
            fw_1.move_to_operands(fwidth);
            fw_1.move_to_operands(one); // +1 for 0-char
            
            exprt fw_lt_bs;
            
            if(arg_type.id()=="pointer")
              fw_lt_bs=binary_relation_exprt(fw_1, "<=", buffer_size(argument));
            else
            {
              index_exprt index;
              index.array()=argument;
              index.index()=gen_zero(uint_type());
              address_of_exprt aof(index);
              fw_lt_bs=binary_relation_exprt(fw_1, "<=", buffer_size(aof));
            }
            
            assertion->make_assertion(fw_lt_bs);
          }
          else
          {
            // this is a possible overflow.
            assertion->make_assertion(false_exprt());
          }
          
          // now kill the contents
          invalidate_buffer(dest, target, argument, arg_type, it->field_width);
          
          args++;
          break;
        }
        case format_tokent::TEXT:
        case format_tokent::UNKNOWN:
        {          
          // nothing
          break;
        }
        default: // everything else
        {
          const exprt &argument=arguments[argument_start_inx+args];
          const typet &arg_type=ns.follow(argument.type());
          
          goto_programt::targett assignment=dest.add_instruction(ASSIGN);
          assignment->location=target->location;
          
          exprt lhs("dereference", arg_type.subtype());
          lhs.copy_to_operands(argument);
          
          exprt rhs=side_effect_expr_nondett(lhs.type());
          rhs.location()=target->location;
           
          assignment->code=code_assignt(lhs, rhs);
          
          args++;
          break;
        }
      }
    }
  }
  else // non-const format string
  {    
    for(unsigned i=argument_start_inx; i<arguments.size(); i++)
    {    
      const typet &arg_type=ns.follow(arguments[i].type());
      
      // Note: is_string_type() is a `good guess' here. Actually
      // any of the pointers could point into an array. But it
      // would suck if we had to invalidate all variables.
      // Luckily this case isn't needed too often.
      if(is_string_type(arg_type))
      {
        goto_programt::targett assertion=dest.add_instruction();
        assertion->location=target->location;
        assertion->location.set("property", "string");
        std::string comment("format string buffer overflow in ");
        comment += function_name;
        assertion->location.set("comment", comment);

        // as we don't know any field width for the %s that 
        // should be here during runtime, we just report a 
        // possibly false positive
        assertion->make_assertion(false_exprt());
        
        invalidate_buffer(dest, target, arguments[i], arg_type, 0);
      }
      else
      {
        goto_programt::targett assignment = dest.add_instruction(ASSIGN);
        assignment->location=target->location;
        
        exprt lhs("dereference", arg_type.subtype());
        lhs.copy_to_operands(arguments[i]);
        
        exprt rhs=side_effect_expr_nondett(lhs.type());
        rhs.location()=target->location;
         
        assignment->code=code_assignt(lhs, rhs);
      }
    }
  }
}

/*******************************************************************\

Function: string_instrumentationt::do_strncmp 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_strncmp(
  goto_programt &dest,
  goto_programt::targett target,
  code_function_callt &call)
{
}

/*******************************************************************\

Function: string_instrumentationt::do_strchr  

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_strchr(
  goto_programt &dest,
  goto_programt::targett target,
  code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()!=2)
  {
    err_location(target->location);
    throw "strchr expected to have two arguments";
  }
  
  goto_programt tmp;

  goto_programt::targett assertion=tmp.add_instruction();
  assertion->make_assertion(is_zero_string(arguments[0]));
  assertion->location=target->location;
  assertion->location.set("property", "string");
  assertion->location.set("comment", "zero-termination of string argument of strchr");

  target->make_skip();
  dest.insert_before_swap(target, tmp);
}

/*******************************************************************\

Function: string_instrumentationt::do_strrchr 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_strrchr(
  goto_programt &dest,
  goto_programt::targett target,
  code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()!=2)
  {
    err_location(target->location);
    throw "strrchr expected to have two arguments";
  }
  
  goto_programt tmp;

  goto_programt::targett assertion=tmp.add_instruction();
  assertion->make_assertion(is_zero_string(arguments[0]));
  assertion->location=target->location;
  assertion->location.set("property", "string");
  assertion->location.set("comment", "zero-termination of string argument of strrchr");

  target->make_skip();
  dest.insert_before_swap(target, tmp);
}

/*******************************************************************\

Function: string_instrumentationt::do_strstr  

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_strstr(
  goto_programt &dest,
  goto_programt::targett target,
  code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()!=2)
  {
    err_location(target->location);
    throw "strstr expected to have two arguments";
  }
  
  goto_programt tmp;

  goto_programt::targett assertion0=tmp.add_instruction();
  assertion0->make_assertion(is_zero_string(arguments[0]));
  assertion0->location=target->location;
  assertion0->location.set("property", "string");
  assertion0->location.set("comment", "zero-termination of 1st string argument of strstr");

  goto_programt::targett assertion1=tmp.add_instruction();
  assertion1->make_assertion(is_zero_string(arguments[1]));
  assertion1->location=target->location;
  assertion1->location.set("property", "string");
  assertion1->location.set("comment", "zero-termination of 2nd string argument of strstr");

  target->make_skip();
  dest.insert_before_swap(target, tmp);
}

/*******************************************************************\

Function: string_instrumentationt::do_strtok  

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_strtok(
  goto_programt &dest,
  goto_programt::targett target,
  code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()!=2)
  {
    err_location(target->location);
    throw "strtok expected to have two arguments";
  }
  
  goto_programt tmp;

  goto_programt::targett assertion0=tmp.add_instruction();
  assertion0->make_assertion(is_zero_string(arguments[0]));
  assertion0->location=target->location;
  assertion0->location.set("property", "string");
  assertion0->location.set("comment", "zero-termination of 1st string argument of strtok");

  goto_programt::targett assertion1=tmp.add_instruction();
  assertion1->make_assertion(is_zero_string(arguments[1]));
  assertion1->location=target->location;
  assertion1->location.set("property", "string");
  assertion1->location.set("comment", "zero-termination of 2nd string argument of strtok");

  target->make_skip();
  dest.insert_before_swap(target, tmp);
}

/*******************************************************************\

Function: string_instrumentationt::do_strerror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::do_strerror(
  goto_programt &dest,
  goto_programt::targett it,
  code_function_callt &call)
{
  if(call.lhs().is_nil())
  {
    it->make_skip();
    return;
  }

  irep_idt identifier_buf="c::__strerror_buffer";
  irep_idt identifier_size="c::__strerror_buffer_size";

  if(context.symbols.find(identifier_buf)==context.symbols.end())
  {
    symbolt new_symbol_size;
    new_symbol_size.base_name="__strerror_buffer_size";
    new_symbol_size.pretty_name=new_symbol_size.base_name;
    new_symbol_size.name=identifier_size;
    new_symbol_size.mode="C";
    new_symbol_size.type=uint_type();
    new_symbol_size.is_statevar=true;
    new_symbol_size.lvalue=true;
    new_symbol_size.static_lifetime=true;

    array_typet type;
    type.subtype()=char_type();
    type.size()=symbol_expr(new_symbol_size);
    symbolt new_symbol_buf;
    new_symbol_buf.mode="C";
    new_symbol_buf.type=type;
    new_symbol_buf.is_statevar=true;
    new_symbol_buf.lvalue=true;
    new_symbol_buf.static_lifetime=true;
    new_symbol_buf.base_name="__strerror_buffer";
    new_symbol_buf.pretty_name=new_symbol_buf.base_name;
    new_symbol_buf.name="c::"+id2string(new_symbol_buf.base_name);

    context.move(new_symbol_buf);
    context.move(new_symbol_size);
  }

  const symbolt &symbol_size=ns.lookup(identifier_size);
  const symbolt &symbol_buf=ns.lookup(identifier_buf);

  goto_programt tmp;

  {  
    goto_programt::targett assignment1=tmp.add_instruction(ASSIGN);
    exprt nondet_size=side_effect_expr_nondett(uint_type());

    assignment1->code=code_assignt(symbol_expr(symbol_size), nondet_size);
    assignment1->location=it->location;
    
    goto_programt::targett assumption1=tmp.add_instruction();

    assumption1->make_assumption(binary_relation_exprt(
      symbol_expr(symbol_size), "notequal",
      gen_zero(symbol_size.type)));

    assumption1->location=it->location;
  }

  // return a pointer to some magic buffer
  exprt index=exprt("index", char_type());
  index.copy_to_operands(symbol_expr(symbol_buf), gen_zero(uint_type()));

  exprt ptr=exprt("address_of", pointer_typet());
  ptr.type().subtype()=char_type();
  ptr.copy_to_operands(index);

  // make that zero-terminated
  {
    goto_programt::targett assignment2=tmp.add_instruction(ASSIGN);
    assignment2->code=code_assignt(is_zero_string(ptr, true), true_exprt());
    assignment2->location=it->location;
  }

  // assign address
  {
    goto_programt::targett assignment3=tmp.add_instruction(ASSIGN);
    exprt rhs=ptr;
    make_type(rhs, call.lhs().type());
    assignment3->code=code_assignt(call.lhs(), rhs);
    assignment3->location=it->location;
  }

  it->make_skip();
  dest.insert_before_swap(it, tmp);
}

/*******************************************************************\

Function: string_instrumentationt::invalidate_buffer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void string_instrumentationt::invalidate_buffer(
  goto_programt &dest,
  goto_programt::const_targett target,
  const exprt &buffer,
  const typet &buf_type,
  const mp_integer &limit)
{
  irep_idt cntr_id="string_instrumentation::$counter";
  
  if(context.symbols.find(cntr_id)==context.symbols.end())
  {
    symbolt new_symbol;
    new_symbol.base_name="$counter";
    new_symbol.pretty_name=new_symbol.base_name;
    new_symbol.name=cntr_id;
    new_symbol.mode="C";
    new_symbol.type=uint_type();
    new_symbol.is_statevar=true;
    new_symbol.lvalue=true;
    new_symbol.static_lifetime=true;
    
    context.move(new_symbol);
  }
  
  const symbolt &cntr_sym=ns.lookup(cntr_id);
  
  // create a loop that runs over the buffer
  // and invalidates every element
  
  goto_programt::targett init=dest.add_instruction(ASSIGN);
  init->location=target->location;  
  init->code=code_assignt(symbol_expr(cntr_sym), gen_zero(cntr_sym.type));
  
  goto_programt::targett check=dest.add_instruction();
  check->location=target->location;  
  
  goto_programt::targett invalidate=dest.add_instruction(ASSIGN);
  invalidate->location=target->location;  
  
  goto_programt::targett increment=dest.add_instruction(ASSIGN);
  increment->location=target->location;  
  
  exprt plus("+", uint_type());
  plus.copy_to_operands(symbol_expr(cntr_sym));
  plus.copy_to_operands(gen_one(uint_type()));
  
  increment->code=code_assignt(symbol_expr(cntr_sym), plus);
  
  goto_programt::targett back=dest.add_instruction();
  back->location=target->location;  
  back->make_goto(check);
  back->guard=true_exprt();
  
  goto_programt::targett exit=dest.add_instruction();
  exit->location=target->location;  
  exit->make_skip();  
  
  exprt cnt_bs, bufp;
  
  if(buf_type.id()=="pointer")
    bufp = buffer;
  else
  {
    index_exprt index;
    index.array()=buffer;
    index.index()=gen_zero(uint_type());
    index.type()=buf_type.subtype();
    bufp = address_of_exprt(index);
  }
  
  exprt deref("dereference", buf_type.subtype());
  exprt b_plus_i("+", bufp.type());
  b_plus_i.copy_to_operands(bufp);
  b_plus_i.copy_to_operands(symbol_expr(cntr_sym));
  deref.copy_to_operands(b_plus_i);
  
  check->make_goto(exit);
  
  if(limit==0)
    check->guard=
          binary_relation_exprt(symbol_expr(cntr_sym), ">=", 
                                buffer_size(bufp));
  else
    check->guard=
          binary_relation_exprt(symbol_expr(cntr_sym), ">", 
                                from_integer(limit, uint_type()));
  
  exprt nondet=side_effect_expr_nondett(buf_type.subtype());
  invalidate->code=code_assignt(deref, nondet);
}
