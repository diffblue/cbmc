/*******************************************************************\

Module: Taint Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/prefix.h>

#include <analyses/custom_bitvector_analysis.h>

#include "taint_analysis.h"
#include "taint_parser.h"

/*******************************************************************\

   Class: taint_analysist

 Purpose:

\*******************************************************************/

class taint_analysist:public messaget
{
public:
  taint_analysist(
    const namespacet &_ns):
    ns(_ns)
  {
  }

  bool operator()(
    const std::string &taint_file_name,
    goto_functionst &goto_functions);

protected:
  const namespacet &ns;
  taint_parse_treet taint;
  
  void instrument(goto_functionst &);
  void instrument(goto_functionst::goto_functiont &);
};

/*******************************************************************\

Function: taint_analysist::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void taint_analysist::instrument(goto_functionst &goto_functions)
{
  for(auto & function : goto_functions.function_map)
    instrument(function.second);
}

/*******************************************************************\

Function: taint_analysist::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void taint_analysist::instrument(
  goto_functionst::goto_functiont &goto_function)
{
  for(goto_programt::instructionst::iterator
      it=goto_function.body.instructions.begin();
      it!=goto_function.body.instructions.end();
      it++)
  {
    const goto_programt::instructiont &instruction=*it;
    
    goto_programt tmp;
  
    switch(instruction.type)
    {
    case FUNCTION_CALL:
      {
        const code_function_callt &function_call=
          to_code_function_call(instruction.code);
        const exprt &function=function_call.function();
        if(function.id()==ID_symbol)
        {
          const irep_idt &identifier=
            to_symbol_expr(function).get_identifier();
        
          for(const auto & e : taint.rules)
          {
            if(has_prefix(id2string(identifier), "java::"+id2string(e.function_identifier)+":"))
            {
              status() << "MATCH " << identifier << eom;
              
              switch(e.kind)
              {
              case taint_parse_treet::rulet::SOURCE:
                {
                  codet code_set_may("set_may");
                  code_set_may.operands().resize(2);
                  goto_programt::targett t=tmp.add_instruction();
                  t->make_other(code_set_may);
                  t->source_location=instruction.source_location;
                }
                break;
              
              case taint_parse_treet::rulet::SINK:
                {
                  goto_programt::targett t=tmp.add_instruction();
                  binary_predicate_exprt get_may("get_may");
                  t->make_assertion(get_may);
                  t->source_location=instruction.source_location;
                }
                break;
              
              case taint_parse_treet::rulet::SANITIZER:
                {
                  codet code_set_may("clear_may");
                  code_set_may.operands().resize(2);
                  goto_programt::targett t=tmp.add_instruction();
                  t->make_other(code_set_may);
                  t->source_location=instruction.source_location;
                }
                break;
              }
              
            }
          }
        }
      }
      break;
    
    default:;
    }
    
    if(!tmp.empty())
    {
      goto_programt::targett next=it;
      next++;
      goto_function.body.destructive_insert(next, tmp);
    }
  }
}

/*******************************************************************\

Function: taint_analysist::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool taint_analysist::operator()(
  const std::string &taint_file_name,
  goto_functionst &goto_functions)
{
  try
  {
    status() << "Reading taint file `" << taint_file_name
             << "'" << eom;

    if(taint_parser(taint_file_name, taint, get_message_handler()))
    {
      error() << "Failed to read taint definition file" << eom;
      return true;
    }

    status() << "Got " << taint.rules.size()
             << " taint definitions" << eom;

    taint.output(debug());
    debug() << eom;

    status() << "Instrumenting taint" << eom;

    instrument(goto_functions);
    goto_functions.update();

    status() << "Data-flow analysis" << eom;

    custom_bitvector_analysist custom_bitvector_analysis;
    custom_bitvector_analysis(goto_functions, ns);

    custom_bitvector_analysis.output(ns, goto_functions, std::cout);
    
    //custom_bitvector_analysis.check(ns, goto_functions, cmdline.isset("xml-ui"), std::cout);

    return false;
  }
  catch(const char *error_msg)
  {
    error() << error_msg << eom;
    return true;
  }
  catch(const std::string &error_msg)
  {
    error() << error_msg << eom;
    return true;
  }
  catch(...)
  {
    return true;
  }
}

/*******************************************************************\

Function: taint_analysis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool taint_analysis(
  goto_functionst &goto_functions,
  const namespacet &ns,
  const std::string &taint_file_name,
  message_handlert &message_handler)
{
  taint_analysist taint_analysis(ns);
  taint_analysis.set_message_handler(message_handler);
  return taint_analysis(taint_file_name, goto_functions);
}

