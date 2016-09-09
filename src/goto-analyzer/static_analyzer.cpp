/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <fstream>

#include <util/json.h>
#include <util/xml.h>

#include <analyses/interval_domain.h>
#include <analyses/constant_propagator.h>

#include "static_analyzer.h"

template<class analyzerT>
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


/// Run the analysis, check the assertions and report in the correct format.
/// \return false on success, true on failure. 
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


/// Check the assertions and give results as text via out.
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

      exprt simplified=domain[i_it].domain_simplify(i_it->guard, ns);

      result() << '[' << i_it->source_location.get_property_id()
               << ']' << ' ';

      result() << i_it->source_location;
      if(!i_it->source_location.get_comment().empty())
        result() << ", " << i_it->source_location.get_comment();
      result() << ": ";
      if(simplified.is_true())
        { result() << "SUCCESS"; pass++; }
      else if(simplified.is_false())
        { result() << "FAILURE (if reachable)"; fail++; }
      else
        { result() << "UNKNOWN"; unknown++; }
      result() << eom;

    }

    status() << '\n';
  }
  status() << "SUMMARY: " << pass << " pass, " << fail << " fail if reachable, "
           << unknown << " unknown\n";
}


/// Check the assertions and give results as JSON via out. 
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

      exprt simplified=domain[i_it].domain_simplify(i_it->guard, ns);

      json_objectt &j=json_result.push_back().make_object();

      if(simplified.is_true())
        j["status"]=json_stringt("SUCCESS");
      else if(simplified.is_false())
        j["status"]=json_stringt("FAILURE (if reachable)");
      else
        j["status"]=json_stringt("UNKNOWN");

      j["file"]=json_stringt(id2string(i_it->source_location.get_file()));
      j["line"]=json_numbert(id2string(i_it->source_location.get_line()));
      j["description"]=json_stringt(id2string(
        i_it->source_location.get_comment()));
    }
  }
  status() << "Writing JSON report" << eom;
  out << json_result;
}


/// Check the assertions and give results as XML via out.
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

      exprt simplified=domain[i_it].domain_simplify(i_it->guard, ns);

      xmlt &x=xml_result.new_element("result");

      if(simplified.is_true())
        x.set_attribute("status", "SUCCESS");
      else if(simplified.is_false())
        x.set_attribute("status", "FAILURE (if reachable)");
      else
        x.set_attribute("status", "UNKNOWN");

      x.set_attribute("file", id2string(i_it->source_location.get_file()));
      x.set_attribute("line", id2string(i_it->source_location.get_line()));
      x.set_attribute(
        "description", id2string(i_it->source_location.get_comment()));
    }
  }

  status() << "Writing XML report" << eom;
  out << xml_result;
}

/// Runs the analyzer, check assertions and generate a report via out
/// \param goto_model : the program to check
/// \param options : the options giving the domain and output
/// \param out : the output channel to use
/// \return false on success, true on failure
bool static_analyzer(
  const goto_modelt &goto_model,
  const optionst &options,
  message_handlert &message_handler,
  std::ostream &out)
{
  if(options.get_bool_option("flow-sensitive"))
  {
    if(options.get_bool_option("constants"))
      return static_analyzert<ait<constant_propagator_domaint> >
        (goto_model, options, message_handler, out)();

    else if(options.get_bool_option("intervals"))
      return static_analyzert<ait<interval_domaint> >
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
      return static_analyzert<concurrency_aware_ait<constant_propagator_domaint> >
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
  m.status() << "Task / Interpreter / Domain combination not supported" << messaget::eom;
  return true;
}
