/*******************************************************************\

Module: Assembler -> Goto

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ansi-c/string_constant.h>
#include <assembler/assembler_parser.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::convert_asm

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_asm(
  const codet &code,
  goto_programt &dest)
{
  if(code.get(ID_flavor)==ID_gcc)
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
        ab->location=code.location();

        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->location=code.location();
        t->code=codet(ID_fence);
        t->code.location()=code.location();
        t->code.set(ID_WWfence, true);
        t->code.set(ID_RRfence, true);
        t->code.set(ID_RWfence, true);
        t->code.set(ID_WRfence, true);
      }
        
      if(command=="mfence" ||
         command=="lfence" ||
         command=="sfence") // x86
      {
        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->location=code.location();
        t->code=codet(ID_fence);
        t->code.location()=code.location();
        t->code.set(ID_WWfence, true);
        t->code.set(ID_RRfence, true);
        t->code.set(ID_RWfence, true);
        t->code.set(ID_WRfence, true);
      }
      else if(command=="sync") // Power
      {
        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->location=code.location();
        t->code=codet(ID_fence);
        t->code.location()=code.location();
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
        t->location=code.location();
        t->code=codet(ID_fence);
        t->code.location()=code.location();
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
        t->location=code.location();
        t->code=codet(ID_fence);
        t->code.location()=code.location();
        // doesn't do anything by itself,
        // needs to be combined with branch
      }
      else if(command=="dmb" || command=="dsb") // ARM
      {
        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->location=code.location();
        t->code=codet(ID_fence);
        t->code.location()=code.location();
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
        t->location=code.location();
        t->code=codet(ID_fence);
        t->code.location()=code.location();
        // doesn't do anything by itself,
        // needs to be combined with branch
      }
      else
        unknown=true; // give up

      if(x86_32_locked_atomic)
      {
        goto_programt::targett ae=tmp_dest.add_instruction(ATOMIC_END);
        ae->location=code.location();

        x86_32_locked_atomic=false;
      }
    }
    
    if(unknown)
      copy(code, OTHER, dest);
    else
      dest.destructive_append(tmp_dest);
  }
  else
  {
    // give up and copy as OTHER
    copy(code, OTHER, dest);  
  }
}
