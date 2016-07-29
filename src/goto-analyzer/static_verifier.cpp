/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "static_verifier.h"



/*******************************************************************\

Function: static_verifiertt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool static_verifiert::operator()()
{
  status() << "performing interval analysis" << eom;
  interval_analysis(goto_functions, ns);

  if(!options.get_option("json").empty())
    json_report(options.get_option("json"));
  else if(!options.get_option("xml").empty())
    xml_report(options.get_option("xml"));
  else
    plain_text_report();

  return false;
}

/*******************************************************************\

Function: static_verifiert::plain_text_report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_verifiert::plain_text_report()
{
  unsigned pass=0, fail=0, unknown=0;

  if (constant_propagation)
    propagate_constants();

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

      result() << '[' << i_it->source_location.get_property_id()
               << ']' << ' ';

      result() << i_it->source_location;
      if(!i_it->source_location.get_comment().empty())
        result() << ", " << i_it->source_location.get_comment();
      result() << ": ";
      if(r.is_true())
        result() << "SUCCESS";
      else if(r.is_false())
        result() << "FAILURE";
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

Function: static_verifiert::json_report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_verifiert::json_report(const std::string &file_name)
{
  json_arrayt json_result;

  if (constant_propagation)
    propagate_constants();

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

  std::ofstream out(file_name);
  if(!out)
  {
    error() << "failed to open JSON output file `"
            << file_name << "'" << eom;
    return;
  }

  status() << "Writing report to `" << file_name << "'" << eom;
  out << json_result;
}

/*******************************************************************\

Function: static_verifiert::xml_report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void static_verifiert::xml_report(const std::string &file_name)
{
  xmlt xml_result;

  if (constant_propagation)
    propagate_constants();

  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body.has_assertion()) continue;

    if(f_it->first=="__actual_thread_spawn")
      continue;

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_assert()) continue;

      tvt r=eval(i_it);

      xmlt &x=xml_result.new_element("result");

      if(r.is_true())
        x.set_attribute("status", "SUCCESS");
      else if(r.is_false())
        x.set_attribute("status", "FAILURE");
      else
        x.set_attribute("status", "UNKNOWN");

      x.set_attribute("file", id2string(i_it->source_location.get_file()));
      x.set_attribute("line", id2string(i_it->source_location.get_line()));
      x.set_attribute("description", id2string(i_it->source_location.get_comment()));
    }
  }

  std::ofstream out(file_name);
  if(!out)
  {
    error() << "failed to open XML output file `"
            << file_name << "'" << eom;
    return;
  }

  status() << "Writing report to `" << file_name << "'" << eom;
  out << xml_result;
}
