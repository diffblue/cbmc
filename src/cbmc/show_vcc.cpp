/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <fstream>

#include <langapi/mode.h>
#include <langapi/languages.h>
#include <langapi/language_util.h>

#include <ansi-c/ansi_c_language.h>

#include "bmc.h"

/*******************************************************************\

Function: bmct::show_vcc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmct::show_vcc(std::ostream &out)
{
  switch(ui)
  {
  case ui_message_handlert::OLD_GUI:
  case ui_message_handlert::XML_UI:
    error("not supported");
    return;
    
  case ui_message_handlert::PLAIN:
    break;
    
  default:
    assert(false);
  }   
    
  out << std::endl << "VERIFICATION CONDITIONS:" << std::endl << std::endl;

  languagest languages(ns, new_ansi_c_language());

  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
  {
    if(!it->is_assert()) continue;
    
    if(it->source.pc->location.is_not_nil())
      out << it->source.pc->location << std::endl;
    
    if(it->comment!="")
      out << it->comment << std::endl;
      
    out << "Priority " << it->priority << std::endl;

    symex_target_equationt::SSA_stepst::const_iterator
      p_it=equation.SSA_steps.begin();
      
    for(unsigned count=1; p_it!=it; p_it++)
      if(p_it->is_assume() || p_it->is_assignment())
        if(!p_it->ignore)
        {
          std::string string_value;
          languages.from_expr(p_it->cond_expr, string_value);
          out << "{-" << count << "} " << string_value << std::endl;

          #if 0
          languages.from_expr(p_it->guard_expr, string_value);
          out << "GUARD: " << string_value << std::endl;
          out << std::endl;
          #endif
          
          count++;
        }

    out << "|--------------------------" << std::endl;

    std::string string_value;
    languages.from_expr(it->cond_expr, string_value);
    out << "{" << 1 << "} " << string_value << std::endl;
    
    out << std::endl;
  }
}

/*******************************************************************\

Function: bmct::show_vcc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bmct::show_vcc()
{
  const std::string &filename=options.get_option("outfile");
  
  if(filename.empty() || filename=="-")
    show_vcc(std::cout);
  else
  {
    std::ofstream out(filename.c_str());
    if(!out)
      std::cerr << "failed to open " << filename << std::endl;
    else
      show_vcc(out);
  }
}

