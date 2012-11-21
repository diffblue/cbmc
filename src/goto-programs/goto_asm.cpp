/*******************************************************************\

Module: Assembler -> Goto

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ansi-c/string_constant.h>

#include "goto_convert_class.h"

/*******************************************************************\

Function: goto_convertt::convert_asm

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_convertt::convert_asm(const codet &code, goto_programt &dest)
{
  if(code.get(ID_flavor)==ID_gcc)
  {
    const irep_idt &i_str=
      to_string_constant(code.op0()).get_value();

    std::istringstream str(id2string(i_str));
    
    goto_programt tmp_dest;
    bool unknown=false;

    std::string line;
    while(std::getline(str, line))
    {
      // remove comments
      std::string::size_type c=line.find("#");
      if(c!=std::string::npos) line.resize(c);

      // remove leading whitespace
      c=line.find_first_not_of(" \t");
      if(c!=std::string::npos) line.erase(0, c);

      // remove trailing whitespace
      c=line.find_last_not_of(" \t");
      if(c!=std::string::npos) line.resize(c+1);

      if(line.empty()) continue;

      if(line=="mfence") // x86
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
      else if(line=="sync") // Power
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
      else if(line=="lwsync") // Power
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
      else if(line=="isync") // Power
      {
        goto_programt::targett t=tmp_dest.add_instruction(OTHER);
        t->location=code.location();
        t->code=codet(ID_fence);
        t->code.location()=code.location();
        // doesn't do anything by itself,
        // needs to be combined with branch
      }
      else if(line=="dmb" || line=="dsb") // ARM
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
      else if(line=="isb") // ARM
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
