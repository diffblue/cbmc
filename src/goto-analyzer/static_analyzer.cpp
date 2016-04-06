/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/threeval.h>
#include <util/json.h>

#include "static_analyzer.h"

class static_analyzert:public messaget
{
public:
  static_analyzert(
    const goto_functionst &_goto_functions,
    const namespacet &_ns,
    const optionst &_options,
    message_handlert &_message_handler):
    goto_functions(_goto_functions),
    ns(_ns),
    options(_options),
    message_handler(_message_handler)
  {
  }
  
  bool operator()();

protected:
  const goto_functionst &goto_functions;
  const namespacet &ns;
  const optionst &options;
  message_handlert &message_handler;

  void plain_text_report();
  void json_report();  
  
  tvt eval(goto_programt::const_targett)
  {
    return tvt::unknown();
  }
};

/*******************************************************************\

Function: static_analyzert::operator()

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool static_analyzert::operator()()
{
  if(!options.get_option("json").empty())
    json_report();
  else
    plain_text_report();

  return false;
}
  
/*******************************************************************\

Function: static_analyzert::plain_text_report

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void static_analyzert::plain_text_report()
{
  unsigned pass=0, fail=0, unknown=0;
  
  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body.has_assertion()) continue;
    
    if(f_it->first=="__actual_thread_spawn")
      continue;

    status() << "******** Function " << f_it->first << eom;

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_assert()) continue;
      
      tvt r=eval(i_it);

      result() << i_it->source_location;
      if(!i_it->source_location.get_comment().empty())
        result() << ", " << i_it->source_location.get_comment();
      result() << ": ";
      if(r.is_true())
        result() << "TRUE";
      else if(r.is_false())
        result() << "FALSE";
      else
        result() << "UNKNOWN";
      result() << eom;

      if(r.is_true())
        pass++;
      else if(r.is_false())
        fail++;
      else
        unknown++;
    }

    status() << '\n';
  }
  
  status() << "SUMMARY: " << pass << " pass, " << fail << " fail, "
           << unknown << " unknown\n";
}

/*******************************************************************\

Function: static_analyzert::json_report

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void static_analyzert::json_report()
{  
  json_arrayt json_result;
  
  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body.has_assertion()) continue;
    
    if(f_it->first=="__actual_thread_spawn")
      continue;

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_assert()) continue;
      
      tvt r=eval(i_it);

      json_objectt &j=json_result.push_back().make_object();

      if(r.is_true())
        j["status"]=json_stringt("SUCCESS");
      else if(r.is_false())
        j["status"]=json_stringt("FAILURE");
      else 
        j["status"]=json_stringt("UNKNOWN");

      j["file"]=json_stringt(id2string(i_it->source_location.get_file()));
      j["line"]=json_numbert(id2string(i_it->source_location.get_line()));      
      j["description"]=json_stringt(id2string(
        i_it->source_location.get_comment()));
    }
  }
}

/*******************************************************************\

Function: static_analyzer

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool static_analyzer(
  const goto_functionst &goto_functions,
  const namespacet &ns,
  const optionst &options,
  message_handlert &message_handler)
{
  return static_analyzert(
    goto_functions, ns, options, message_handler)();
}
