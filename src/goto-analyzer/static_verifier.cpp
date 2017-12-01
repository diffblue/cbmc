/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#include "static_verifier.h"

#include <util/xml.h>
#include <util/xml_expr.h>
#include <util/json.h>
#include <util/json_expr.h>


/// Runs the analyzer and then prints out the domain
/// \param goto_model: the program analyzed
/// \param ai: the abstract interpreter after it has been run to fix point
/// \param options: the parsed user options
/// \param message_handler: the system message handler
/// \param out: output stream for the printing
/// \return: false on success with the domain printed to out
bool static_verifier(
  const goto_modelt &goto_model,
  const ai_baset &ai,
  const optionst &options,
  message_handlert &message_handler,
  std::ostream &out)
{
  std::size_t pass=0, fail=0, unknown=0;

  namespacet ns(goto_model.symbol_table);

  messaget m(message_handler);
  m.status() << "Checking assertions" << messaget::eom;

  if(options.get_bool_option("json"))
  {
    json_arrayt json_result;

    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      m.progress() << "Checking " << f_it->first << messaget::eom;

      if(!f_it->second.body.has_assertion())
        continue;

      forall_goto_program_instructions(i_it, f_it->second.body)
      {
        if(!i_it->is_assert())
          continue;

        exprt e(i_it->guard);
        const ai_domain_baset &domain(ai.abstract_state_before(i_it));
        domain.ai_simplify(e, ns);

        json_objectt &j=json_result.push_back().make_object();

        if(e.is_true())
        {
          j["status"]=json_stringt("SUCCESS");
          ++pass;
        }
        else if(e.is_false())
        {
          j["status"]=json_stringt("FAILURE (if reachable)");
          ++fail;
        }
        else if(domain.is_bottom())
        {
          j["status"]=json_stringt("SUCCESS (unreachable)");
          ++pass;
        }
        else
        {
          j["status"]=json_stringt("UNKNOWN");
          ++unknown;
        }

        j["sourceLocation"]=json(i_it->source_location);
      }
    }
    m.status() << "Writing JSON report" << messaget::eom;
    out << json_result;
  }
  else if(options.get_bool_option("xml"))
  {
    xmlt xml_result;

    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      m.progress() << "Checking " << f_it->first << messaget::eom;

      if(!f_it->second.body.has_assertion())
        continue;

      forall_goto_program_instructions(i_it, f_it->second.body)
      {
        if(!i_it->is_assert())
          continue;

        exprt e(i_it->guard);
        const ai_domain_baset &domain(ai.abstract_state_before(i_it));
        domain.ai_simplify(e, ns);

        xmlt &x=xml_result.new_element("result");

        if(e.is_true())
        {
          x.set_attribute("status", "SUCCESS");
          ++pass;
        }
        else if(e.is_false())
        {
          x.set_attribute("status", "FAILURE (if reachable)");
          ++fail;
        }
        else if(domain.is_bottom())
        {
          x.set_attribute("status", "SUCCESS (unreachable)");
          ++pass;
        }
        else
        {
          x.set_attribute("status", "UNKNOWN");
          ++unknown;
        }

        x.set_attribute("file", id2string(i_it->source_location.get_file()));
        x.set_attribute("line", id2string(i_it->source_location.get_line()));
        x.set_attribute(
          "description",
          id2string(i_it->source_location.get_comment()));
      }
    }

    m.status() << "Writing XML report" << messaget::eom;
    out << xml_result;
  }
  else
  {
    INVARIANT(options.get_bool_option("text"), "Other output formats handled");

    forall_goto_functions(f_it, goto_model.goto_functions)
    {
      m.progress() << "Checking " << f_it->first << messaget::eom;

      if(!f_it->second.body.has_assertion())
        continue;

      out << "******** Function " << f_it->first << '\n';

      forall_goto_program_instructions(i_it, f_it->second.body)
      {
        if(!i_it->is_assert())
          continue;

        exprt e(i_it->guard);
        const ai_domain_baset &domain(ai.abstract_state_before(i_it));
        domain.ai_simplify(e, ns);

        out << '[' << i_it->source_location.get_property_id()
            << ']' << ' ';

        out << i_it->source_location;

        if(!i_it->source_location.get_comment().empty())
          out << ", " << i_it->source_location.get_comment();

        out << ": ";

        if(e.is_true())
        {
          out << "Success";
          pass++;
        }
        else if(e.is_false())
        {
          out << "Failure (if reachable)";
          fail++;
        }
        else if(domain.is_bottom())
        {
          out << "Success (unreachable)";
          pass++;
        }
        else
        {
          out << "Unknown";
          unknown++;
        }

        out << '\n';
      }

      out << '\n';
    }
  }

  m.status() << "Summary: "
             << pass << " pass, "
             << fail << " fail if reachable, "
             << unknown << " unknown\n";

  return false;
}
