/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#include "static_verifier.h"

#include <util/json_expr.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>

#include <analyses/ai.h>

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
  std::size_t pass = 0, fail = 0, unknown = 0;

  namespacet ns(goto_model.symbol_table);

  messaget m(message_handler);
  m.status() << "Checking assertions" << messaget::eom;

  struct resultt
  {
    // clang-format off
    enum { TRUE, FALSE, BOTTOM, UNKNOWN } status;
    // clang-format on
    source_locationt source_location;
    irep_idt function_id;
  };

  std::vector<resultt> results;

  for(const auto &f : goto_model.goto_functions.function_map)
  {
    const auto &symbol = ns.lookup(f.first);

    m.progress() << "Checking " << symbol.display_name() << messaget::eom;

    if(!f.second.body.has_assertion())
      continue;

    forall_goto_program_instructions(i_it, f.second.body)
    {
      if(!i_it->is_assert())
        continue;

      exprt e(i_it->guard);
      auto dp = ai.abstract_state_before(i_it);
      const ai_domain_baset &domain(*dp);
      domain.ai_simplify(e, ns);

      results.push_back(resultt());
      auto &result = results.back();

      if(e.is_true())
      {
        result.status = resultt::TRUE;
        ++pass;
      }
      else if(e.is_false())
      {
        result.status = resultt::FALSE;
        ++fail;
      }
      else if(domain.is_bottom())
      {
        result.status = resultt::BOTTOM;
        ++pass;
      }
      else
      {
        result.status = resultt::UNKNOWN;
        ++unknown;
      }

      result.source_location = i_it->source_location;
      result.function_id = f.first;
    }
  }

  if(options.get_bool_option("json"))
  {
    m.status() << "Writing JSON report" << messaget::eom;

    json_arrayt json_result;

    for(const auto &result : results)
    {
      json_objectt &j = json_result.push_back().make_object();

      switch(result.status)
      {
      case resultt::TRUE:
        j["status"] = json_stringt("SUCCESS");
        break;

      case resultt::FALSE:
        j["status"] = json_stringt("FAILURE (if reachable)");
        break;

      case resultt::BOTTOM:
        j["status"] = json_stringt("SUCCESS (unreachable)");
        break;

      case resultt::UNKNOWN:
        j["status"] = json_stringt("UNKNOWN");
        ++unknown;
        break;
      }

      j["sourceLocation"] = json(result.source_location);
    }

    out << json_result;
  }
  else if(options.get_bool_option("xml"))
  {
    m.status() << "Writing XML report" << messaget::eom;

    xmlt xml_result;

    for(const auto &result : results)
    {
      xmlt &x = xml_result.new_element("result");

      switch(result.status)
      {
      case resultt::TRUE:
        x.set_attribute("status", "SUCCESS");
        break;

      case resultt::FALSE:
        x.set_attribute("status", "FAILURE (if reachable)");
        break;

      case resultt::BOTTOM:
        x.set_attribute("status", "SUCCESS (unreachable)");
        break;

      case resultt::UNKNOWN:
        x.set_attribute("status", "UNKNOWN");
      }

      x.set_attribute("file", id2string(result.source_location.get_file()));
      x.set_attribute("line", id2string(result.source_location.get_line()));
      x.set_attribute(
        "description", id2string(result.source_location.get_comment()));
    }

    out << xml_result;
  }
  else if(options.get_bool_option("text"))
  {
    irep_idt last_function_id;

    for(const auto &result : results)
    {
      if(last_function_id != result.function_id)
      {
        if(!last_function_id.empty())
          out << '\n';
        last_function_id = result.function_id;
        const auto &symbol = ns.lookup(last_function_id);
        out << "******** Function " << symbol.display_name() << '\n';
      }

      out << '[' << result.source_location.get_property_id() << ']' << ' ';

      out << result.source_location;

      if(!result.source_location.get_comment().empty())
        out << ", " << result.source_location.get_comment();

      out << ": ";

      switch(result.status)
      {
      case resultt::TRUE:
        out << "Success";
        break;

      case resultt::FALSE:
        out << "Failure (if reachable)";
        break;

      case resultt::BOTTOM:
        out << "Success (unreachable)";
        break;

      case resultt::UNKNOWN:
        out << "Unknown";
        break;
      }

      out << '\n';
    }
  }
  else
  {
    irep_idt last_function_id;

    for(const auto &result : results)
    {
      if(last_function_id != result.function_id)
      {
        if(!last_function_id.empty())
          out << '\n';
        last_function_id = result.function_id;
        const auto &symbol = ns.lookup(last_function_id);
        out << "******** Function " << symbol.display_name() << '\n';
      }

      m.result() << '[' << result.source_location.get_property_id() << ']'
                 << ' ';

      m.result() << result.source_location;

      if(!result.source_location.get_comment().empty())
        m.result() << ", " << result.source_location.get_comment();

      m.result() << ": ";

      switch(result.status)
      {
      case resultt::TRUE:
        m.result() << m.green << "SUCCESS" << m.reset;
        break;

      case resultt::FALSE:
        m.result() << m.red << "FAILURE" << m.reset << " (if reachable)";
        break;

      case resultt::BOTTOM:
        m.result() << m.green << "SUCCESS" << m.reset << " (unreachable)";
        break;

      case resultt::UNKNOWN:
        m.result() << m.yellow << "UNKNOWN" << m.reset;
        break;
      }

      m.result() << messaget::eom;
    }
  }

  m.status() << m.bold << "Summary: "
             << pass << " pass, "
             << fail << " fail if reachable, "
             << unknown << " unknown"
             << m.reset << messaget::eom;

  return false;
}
