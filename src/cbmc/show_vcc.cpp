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
  
  bool has_threads=equation.has_threads();

  for(symex_target_equationt::SSA_stepst::iterator
      s_it=equation.SSA_steps.begin();
      s_it!=equation.SSA_steps.end();
      s_it++)
  {
    if(!s_it->is_assert()) continue;
    
    if(s_it->source.pc->location.is_not_nil())
      out << s_it->source.pc->location << std::endl;
    
    if(s_it->comment!="")
      out << s_it->comment << std::endl;
      
    symex_target_equationt::SSA_stepst::const_iterator
      p_it=equation.SSA_steps.begin();

    // we show everything in case there are threads
    symex_target_equationt::SSA_stepst::const_iterator
      last_it=has_threads?equation.SSA_steps.end():s_it;
      
    for(unsigned count=1; p_it!=last_it; p_it++)
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
    languages.from_expr(s_it->cond_expr, string_value);
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

