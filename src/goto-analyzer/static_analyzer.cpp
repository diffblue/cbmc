/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/json.h>
#include <util/json_expr.h>
#include <util/xml.h>

#include <analyses/interval_domain.h>
#include <analyses/constant_propagator.h>

#include "static_analyzer.h"

template<typename analyzerT>
class static_analyzert:public messaget
{
public:
  static_analyzert(
    const goto_modelt &_goto_model,
    const optionst &_options,
    message_handlert &_message_handler,
    std::ostream &_out):
    messaget(_message_handler),
    goto_functions(_goto_model.goto_functions),
    ns(_goto_model.symbol_table),
    options(_options),
    out(_out)
  {
  }

  bool operator()();

protected:
  const goto_functionst &goto_functions;
  const namespacet ns;
  const optionst &options;
  std::ostream &out;

  // analyses
  analyzerT domain;

  void plain_text_report();
  void json_report();
  void xml_report();
};

/*******************************************************************\

Function: static_analyzert<analyzerT>::operator()

  Inputs: None.

 Outputs: false on success, true on failure.

 Purpose: Run the analysis, check the assertions and report in the
          correct format.

\*******************************************************************/

template<class analyzerT>
bool static_analyzert<analyzerT>::operator()()
{
  status() << "Performing analysis" << eom;
  domain(goto_functions, ns);

  if(options.get_bool_option("json"))
    json_report();
  else if(options.get_bool_option("xml"))
    xml_report();
  else
    plain_text_report();

  return false;
}

/*******************************************************************\

Function: static_analyzert<analyzerT>::plain_text_report

  Inputs: None.

 Outputs: Text report via out.

 Purpose: Check the assertions and give results as text.

\*******************************************************************/

template<class analyzerT>
void static_analyzert<analyzerT>::plain_text_report()
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

      exprt e(i_it->guard);
      domain[i_it].ai_simplify(e, ns);

      result() << '[' << i_it->source_location.get_property_id()
               << ']' << ' ';

      result() << i_it->source_location;

      if(!i_it->source_location.get_comment().empty())
        result() << ", " << i_it->source_location.get_comment();

      result() << ": ";

      if(e.is_true())
      {
        result() << "Success";
        pass++;
      }
      else if(e.is_false())
      {
        result() << "Failure (if reachable)";
        fail++;
      }
      else
      {
        result() << "Unknown";
        unknown++;
      }

      result() << eom;
    }

    status() << '\n';
  }

  status() << "Summary: " << pass << " pass, " << fail << " fail if reachable, "
           << unknown << " unknown\n";
}

/*******************************************************************\

Function: static_analyzert<analyzerT>::json_report

  Inputs: None.

 Outputs: JSON report via out.

 Purpose: Check the assertions and give results as JSON.

\*******************************************************************/

template<class analyzerT>
void static_analyzert<analyzerT>::json_report()
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

      exprt e(i_it->guard);
      domain[i_it].ai_simplify(e, ns);

      json_objectt &j=json_result.push_back().make_object();

      if(e.is_true())
        j["status"]=json_stringt("SUCCESS");
      else if(e.is_false())
        j["status"]=json_stringt("FAILURE (if reachable)");
      else
        j["status"]=json_stringt("UNKNOWN");

      j["sourceLocation"]=json(i_it->source_location);
    }
  }
  status() << "Writing JSON report" << eom;
  out << json_result;
}

/*******************************************************************\

Function: static_analyzert<analyzerT>::xml_report

  Inputs: None.

 Outputs: XML report via out.

 Purpose: Check the assertions and give results as XML.

\*******************************************************************/

template<class analyzerT>
void static_analyzert<analyzerT>::xml_report()
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

      exprt e(i_it->guard);
      domain[i_it].ai_simplify(e, ns);

      xmlt &x=xml_result.new_element("result");

      if(e.is_true())
        x.set_attribute("status", "SUCCESS");
      else if(e.is_false())
        x.set_attribute("status", "FAILURE (if reachable)");
      else
        x.set_attribute("status", "UNKNOWN");

      x.set_attribute("file", id2string(i_it->source_location.get_file()));
      x.set_attribute("line", id2string(i_it->source_location.get_line()));
      x.set_attribute(
        "description",
        id2string(i_it->source_location.get_comment()));
    }
  }

  status() << "Writing XML report" << eom;
  out << xml_result;
}

/*******************************************************************\

Function: static_analyzer

  Inputs: The goto_model to check, options giving the domain and output,
          the message handler and output stream.

 Outputs: Report via out.

 Purpose: Runs the analyzer, check assertions and generate a report.

\*******************************************************************/

bool static_analyzer(
  const goto_modelt &goto_model,
  const optionst &options,
  message_handlert &message_handler,
  std::ostream &out)
{
  if(options.get_bool_option("flow-sensitive"))
  {
    if(options.get_bool_option("constants"))
      return static_analyzert<ait<constant_propagator_domaint>>
        (goto_model, options, message_handler, out)();

    else if(options.get_bool_option("intervals"))
      return static_analyzert<ait<interval_domaint>>
        (goto_model, options, message_handler, out)();

    // else if(options.get_bool_option("non-null"))
    //   return static_analyzert<ait<non_null_domaint> >
    //     (goto_model, options, message_handler, out)();
  }
  else if(options.get_bool_option("concurrent"))
  {
    // Constant and interval don't have merge_shared yet
#if 0
    if(options.get_bool_option("constants"))
      return static_analyzert<concurrency_aware_ait<
        constant_propagator_domaint>>
          (goto_model, options, message_handler, out)();

    else if(options.get_bool_option("intervals"))
      return static_analyzert<concurrency_aware_ait<interval_domaint> >
        (goto_model, options, message_handler, out)();

    // else if(options.get_bool_option("non-null"))
    //   return static_analyzert<concurrency_aware_ait<non_null_domaint> >
    //     (goto_model, options, message_handler, out)();
#endif
  }

  messaget m(message_handler);
  m.status() << "Task / Interpreter / Domain combination not supported"
             << messaget::eom;

  return true;
}
