/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "static_analyzer.h"

#include <fstream>

#include <util/threeval.h>
#include <util/json.h>
#include <util/xml.h>

#include <analyses/interval_domain.h>

class static_analyzert:public messaget
{
public:
  static_analyzert(
    const goto_modelt &_goto_model,
    const optionst &_options,
    message_handlert &_message_handler):
    messaget(_message_handler),
    goto_functions(_goto_model.goto_functions),
    ns(_goto_model.symbol_table),
    options(_options)
  {
  }

  bool operator()();

protected:
  const goto_functionst &goto_functions;
  const namespacet ns;
  const optionst &options;

  // analyses
  ait<interval_domaint> interval_analysis;

  void plain_text_report();
  void json_report(const std::string &);
  void xml_report(const std::string &);

  tvt eval(goto_programt::const_targett);
};

bool static_analyzert::operator()()
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

tvt static_analyzert::eval(goto_programt::const_targett t)
{
  exprt guard=t->guard;
  interval_domaint d=interval_analysis[t];
  d.assume(not_exprt(guard), ns);
  if(d.is_bottom())
    return tvt(true);
  return tvt::unknown();
}

void static_analyzert::plain_text_report()
{
  unsigned pass=0, fail=0, unknown=0;

  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body.has_assertion())
      continue;

    if(f_it->first=="__actual_thread_spawn")
      continue;

    status() << "******** Function " << f_it->first << eom;

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_assert())
        continue;

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

void static_analyzert::json_report(const std::string &file_name)
{
  json_arrayt json_result;

  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body.has_assertion())
      continue;

    if(f_it->first=="__actual_thread_spawn")
      continue;

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_assert())
        continue;

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

void static_analyzert::xml_report(const std::string &file_name)
{
  xmlt xml_result;

  forall_goto_functions(f_it, goto_functions)
  {
    if(!f_it->second.body.has_assertion())
      continue;

    if(f_it->first=="__actual_thread_spawn")
      continue;

    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_assert())
        continue;

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
      x.set_attribute(
        "description", id2string(i_it->source_location.get_comment()));
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

bool static_analyzer(
  const goto_modelt &goto_model,
  const optionst &options,
  message_handlert &message_handler)
{
  return static_analyzert(
    goto_model, options, message_handler)();
}

void show_intervals(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  ait<interval_domaint> interval_analysis;
  interval_analysis(goto_model);
  interval_analysis.output(goto_model, out);
}
