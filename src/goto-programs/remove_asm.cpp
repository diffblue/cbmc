/*******************************************************************\

Module: Remove 'asm' statements by compiling into suitable standard
        code

Author: Daniel Kroening

Date:   December 2014

\*******************************************************************/

#include <sstream>

#include <util/std_expr.h>

#include <ansi-c/string_constant.h>
#include <assembler/assembler_parser.h>

#include "remove_asm.h"

class remove_asmt
{
public:
  inline remove_asmt(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions):
    symbol_table(_symbol_table),
    goto_functions(_goto_functions)
  {
  }
  
  void operator()();
  
protected:
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  void process_instruction(
    goto_programt::instructiont &instruction,
    goto_programt &dest);

  void process_function(
    goto_functionst::goto_functiont &);
    
  void gcc_asm_function_call(
    const irep_idt &function_base_name,
    const codet &code,
    goto_programt &dest);
};

/*******************************************************************\

Function: remove_asmt::gcc_asm_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_asmt::gcc_asm_function_call(
  const irep_idt &function_base_name,
  const codet &code,
  goto_programt &dest)
{
  irep_idt function_identifier=function_base_name;
  
  code_function_callt function_call;
  function_call.lhs().make_nil();

  const pointer_typet void_pointer=pointer_typet(void_typet());
  
  // outputs
  forall_operands(it, code.op1())
  {
    if(it->operands().size()==2)
    {
      function_call.arguments().push_back(
        typecast_exprt(address_of_exprt(it->op1()), void_pointer));
    }
  }

  // inputs
  forall_operands(it, code.op2())
  {
    if(it->operands().size()==2)
    {
      function_call.arguments().push_back(
        typecast_exprt(address_of_exprt(it->op1()), void_pointer));
    }
  }

  code_typet fkt_type;
  fkt_type.return_type()=void_typet();
  fkt_type.make_ellipsis();
  
  symbol_exprt fkt(function_identifier, fkt_type);

  function_call.function()=fkt;

  goto_programt::targett call=dest.add_instruction(FUNCTION_CALL);
  call->code=function_call;
  call->source_location=code.source_location();

  // do we have it?
  if(!symbol_table.has_symbol(function_identifier))
  {
    symbolt symbol;
    
    symbol.name=function_identifier;
    symbol.type=fkt_type;
    symbol.base_name=function_base_name;
    symbol.value=nil_exprt();
    
    symbol_table.add(symbol);
  }
}

/*******************************************************************\

Function: remove_asmt::process_instruction

Inputs:

Outputs:

Purpose: removes assembler

\*******************************************************************/

void remove_asmt::process_instruction(
  goto_programt::instructiont &instruction,
  goto_programt &dest)
{
  const code_asmt &code=to_code_asm(instruction.code);
  
  const irep_idt &flavor=code.get_flavor();

  if(flavor==ID_gcc)
  {
    const irep_idt &i_str=
      to_string_constant(code.op0()).get_value();
      
    //std::cout << "DOING " << i_str << std::endl;

    std::istringstream str(id2string(i_str));
    assembler_parser.clear();
    assembler_parser.in=&str;
    assembler_parser.parse();
    
    goto_programt tmp_dest;
    bool unknown=false;
    bool x86_32_locked_atomic=false;

    for(std::list<assembler_parsert::instructiont>::const_iterator
        it=assembler_parser.instructions.begin();
        it!=assembler_parser.instructions.end();
        it++)
    {
      const assembler_parsert::instructiont &instruction=*it;
      if(instruction.empty()) continue;
      
      #if 0
      std::cout << "A ********************\n";
      for(assembler_parsert::instructiont::const_iterator
          t_it=instruction.begin();
          t_it!=instruction.end();
          t_it++)
      {
        std::cout << "XX: " << t_it->pretty() << std::endl;
      }
      
      std::cout << "B ********************\n";
      #endif
      
      // deal with prefixes
      irep_idt command;
      unsigned pos=0;
      
      if(instruction.front().id()==ID_symbol &&
         instruction.front().get(ID_identifier)=="lock")
      {
        x86_32_locked_atomic=true;
        pos++;
      }
      
      // done?
      if(pos==instruction.size())
        continue;
      
      if(instruction[pos].id()==ID_symbol)
      {
        command=instruction[pos].get(ID_identifier);
        pos++;
      }

      if(command=="xchg" || command=="xchgl")
        x86_32_locked_atomic=true;

      if(x86_32_locked_atomic)
      {
        goto_programt::targett ab=tmp_dest.add_instruction(ATOMIC_BEGIN);
        ab->source_location=code.source_location();

        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->source_location=code.source_location();
        t->code=codet(ID_fence);
        t->code.add_source_location()=code.source_location();
        t->code.set(ID_WWfence, true);
        t->code.set(ID_RRfence, true);
        t->code.set(ID_RWfence, true);
        t->code.set(ID_WRfence, true);
      }

      if(command=="fstcw" ||
         command=="fnstcw" ||
         command=="fldcw") // x86
      {
        gcc_asm_function_call("__asm_"+id2string(command), code, tmp_dest);
      }
      else if(command=="mfence" ||
              command=="lfence" ||
              command=="sfence") // x86
      {
        gcc_asm_function_call("__asm_"+id2string(command), code, tmp_dest);
      }
      else if(command=="sync") // Power
      {
        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->source_location=code.source_location();
        t->code=codet(ID_fence);
        t->code.add_source_location()=code.source_location();
        t->code.set(ID_WWfence, true);
        t->code.set(ID_RRfence, true);
        t->code.set(ID_RWfence, true);
        t->code.set(ID_WRfence, true);
        t->code.set(ID_WWcumul, true);
        t->code.set(ID_RWcumul, true);
        t->code.set(ID_RRcumul, true);
        t->code.set(ID_WRcumul, true);
      }
      else if(command=="lwsync") // Power
      {
        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->source_location=code.source_location();
        t->code=codet(ID_fence);
        t->code.add_source_location()=code.source_location();
        t->code.set(ID_WWfence, true);
        t->code.set(ID_RRfence, true);
        t->code.set(ID_RWfence, true);
        t->code.set(ID_WWcumul, true);
        t->code.set(ID_RWcumul, true);
        t->code.set(ID_RRcumul, true);
      }
      else if(command=="isync") // Power
      {
        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->source_location=code.source_location();
        t->code=codet(ID_fence);
        t->code.add_source_location()=code.source_location();
        // doesn't do anything by itself,
        // needs to be combined with branch
      }
      else if(command=="dmb" || command=="dsb") // ARM
      {
        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->source_location=code.source_location();
        t->code=codet(ID_fence);
        t->code.add_source_location()=code.source_location();
        t->code.set(ID_WWfence, true);
        t->code.set(ID_RRfence, true);
        t->code.set(ID_RWfence, true);
        t->code.set(ID_WRfence, true);
        t->code.set(ID_WWcumul, true);
        t->code.set(ID_RWcumul, true);
        t->code.set(ID_RRcumul, true);
        t->code.set(ID_WRcumul, true);
      }
      else if(command=="isb") // ARM
      {
        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->source_location=code.source_location();
        t->code=codet(ID_fence);
        t->code.add_source_location()=code.source_location();
        // doesn't do anything by itself,
        // needs to be combined with branch
      }
      else
        unknown=true; // give up

      if(x86_32_locked_atomic)
      {
        goto_programt::targett ae=tmp_dest.add_instruction(ATOMIC_END);
        ae->source_location=code.source_location();

        x86_32_locked_atomic=false;
      }
    }
    
    if(unknown)
    {
      // we give up; we should perhaps print a warning
    }
    else
      dest.destructive_append(tmp_dest);
  }
}

/*******************************************************************\

Function: remove_asmt::process_function

Inputs:

Outputs:

Purpose: removes assembler

\*******************************************************************/

void remove_asmt::process_function(
  goto_functionst::goto_functiont &goto_function)
{
  Forall_goto_program_instructions(it, goto_function.body)
  {
    if(it->is_other() && it->code.get_statement()==ID_asm)
    {
      goto_programt tmp_dest;
      process_instruction(*it, tmp_dest);
      it->make_skip();
      
      goto_programt::targett next=it;
      next++;
      
      goto_function.body.destructive_insert(next, tmp_dest);
    }
  }
}

/*******************************************************************\

Function: remove_asmt:operator()

Inputs:

Outputs:

Purpose: removes assembler

\*******************************************************************/

void remove_asmt::operator()()
{
  Forall_goto_functions(it, goto_functions)
  {
    process_function(it->second);
  }
}

/*******************************************************************\

Function: remove_asm

Inputs:

Outputs:

Purpose: removes assembler

\*******************************************************************/

void remove_asm(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions)
{
  remove_asmt(symbol_table, goto_functions)();
}

/*******************************************************************\

Function: remove_asm

Inputs:

Outputs:

Purpose: removes assembler

\*******************************************************************/

void remove_asm(goto_modelt &goto_model)
{
  remove_asmt(goto_model.symbol_table, goto_model.goto_functions)();
}

