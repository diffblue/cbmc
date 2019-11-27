/*******************************************************************\

Module: goto-analyzer

Author: Martin Brain, martin.brain@cs.ox.ac.uk

\*******************************************************************/

#include "static_verifier.h"

#include <util/json_irep.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/options.h>
#include <util/range.h>

#include <goto-programs/goto_model.h>

#include <analyses/ai.h>

struct static_verifier_resultt
{
  // clang-format off
  enum statust { TRUE, FALSE, BOTTOM, UNKNOWN } status;
  // clang-format on
  source_locationt source_location;
  irep_idt function_id;
};

void static_verifier(
  const abstract_goto_modelt &abstract_goto_model,
  const ai_baset &ai,
  propertiest &properties)
{
  const namespacet ns{abstract_goto_model.get_symbol_table()};
  // this is mutable because we want to change the property status
  // in this loop
  for(auto &property : properties)
  {
    auto &property_status = property.second.status;
    const goto_programt::const_targett &property_location = property.second.pc;
    exprt condition = property_location->get_condition();
    const std::shared_ptr<const ai_baset::statet> predecessor_state_copy =
      ai.abstract_state_before(property_location);
    // simplify the condition given the domain information we have
    // about the state right before the assertion is evaluated
    predecessor_state_copy->ai_simplify(condition, ns);
    // if the condition simplifies to true the assertion always succeeds
    if(condition.is_true())
    {
      property_status = property_statust::PASS;
    }
    // if the condition simplifies to false the assertion always fails
    else if(condition.is_false())
    {
      property_status = property_statust::FAIL;
    }
    // if the domain state is bottom then the assertion is definitely
    // unreachable
    else if(predecessor_state_copy->is_bottom())
    {
      property_status = property_statust::NOT_REACHABLE;
    }
    // if the condition isn't definitely true, false or unreachable
    // we don't know whether or not it may fail
    else
    {
      property_status = property_statust::UNKNOWN;
    }
  }
}

/// Makes a status message string from a status.
static const char *message(const static_verifier_resultt::statust &status)
{
  switch(status)
  {
  case static_verifier_resultt::TRUE:
    return "SUCCESS";
  case static_verifier_resultt::FALSE:
    return "FAILURE (if reachable)";
  case static_verifier_resultt::BOTTOM:
    return "SUCCESS (unreachable)";
  case static_verifier_resultt::UNKNOWN:
    return "UNKNOWN";
  }
  UNREACHABLE;
}

static void static_verifier_json(
  const std::vector<static_verifier_resultt> &results,
  messaget &m,
  std::ostream &out)
{
  m.status() << "Writing JSON report" << messaget::eom;
  out << make_range(results)
           .map([](const static_verifier_resultt &result) {
             return json_objectt{
               {"status", json_stringt{message(result.status)}},
               {"sourceLocation", json(result.source_location)}};
           })
           .collect<json_arrayt>();
}

static void static_verifier_xml(
  const std::vector<static_verifier_resultt> &results,
  messaget &m,
  std::ostream &out)
{
  m.status() << "Writing XML report" << messaget::eom;

  xmlt xml_result{"cprover"};

  for(const auto &result : results)
  {
    xmlt &x = xml_result.new_element("result");

    switch(result.status)
    {
    case static_verifier_resultt::TRUE:
      x.set_attribute("status", "SUCCESS");
      break;

    case static_verifier_resultt::FALSE:
      x.set_attribute("status", "FAILURE (if reachable)");
      break;

    case static_verifier_resultt::BOTTOM:
      x.set_attribute("status", "SUCCESS (unreachable)");
      break;

    case static_verifier_resultt::UNKNOWN:
      x.set_attribute("status", "UNKNOWN");
    }

    x.set_attribute("file", id2string(result.source_location.get_file()));
    x.set_attribute("line", id2string(result.source_location.get_line()));
    x.set_attribute(
      "description", id2string(result.source_location.get_comment()));
  }

  out << xml_result;
}

static void static_verifier_text(
  const std::vector<static_verifier_resultt> &results,
  const namespacet &ns,
  std::ostream &out)
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
    case static_verifier_resultt::TRUE:
      out << "Success";
      break;

    case static_verifier_resultt::FALSE:
      out << "Failure (if reachable)";
      break;

    case static_verifier_resultt::BOTTOM:
      out << "Success (unreachable)";
      break;

    case static_verifier_resultt::UNKNOWN:
      out << "Unknown";
      break;
    }

    out << '\n';
  }
}

static void static_verifier_console(
  const std::vector<static_verifier_resultt> &results,
  const namespacet &ns,
  messaget &m)
{
  irep_idt last_function_id;
  irep_idt function_file;

  for(const auto &result : results)
  {
    if(last_function_id != result.function_id)
    {
      if(!last_function_id.empty())
        m.status() << '\n';
      last_function_id = result.function_id;
      const auto &symbol = ns.lookup(last_function_id);
      m.status() << messaget::underline << "Function " << symbol.display_name();
      function_file = symbol.location.get_file();
      if(!function_file.empty())
        m.status() << ' ' << function_file;
      if(!symbol.location.get_line().empty())
        m.status() << ':' << symbol.location.get_line();
      m.status() << messaget::reset << messaget::eom;
    }

    m.result() << messaget::faint << '['
               << result.source_location.get_property_id() << ']'
               << messaget::reset;

    if(
      !result.source_location.get_file().empty() &&
      result.source_location.get_file() != function_file)
    {
      m.result() << " file " << result.source_location.get_file();
    }

    if(!result.source_location.get_line().empty())
      m.result() << " line " << result.source_location.get_line();

    if(!result.source_location.get_comment().empty())
      m.result() << ' ' << result.source_location.get_comment();

    m.result() << ": ";

    switch(result.status)
    {
    case static_verifier_resultt::TRUE:
      m.result() << m.green << "SUCCESS" << m.reset;
      break;

    case static_verifier_resultt::FALSE:
      m.result() << m.red << "FAILURE" << m.reset << " (if reachable)";
      break;

    case static_verifier_resultt::BOTTOM:
      m.result() << m.green << "SUCCESS" << m.reset << " (unreachable)";
      break;

    case static_verifier_resultt::UNKNOWN:
      m.result() << m.yellow << "UNKNOWN" << m.reset;
      break;
    }

    m.result() << messaget::eom;
  }

  if(!results.empty())
    m.result() << '\n';
}

static static_verifier_resultt::statust
check_assertion(const ai_domain_baset &domain, exprt e, const namespacet &ns)
{
  if(domain.is_bottom())
  {
    return static_verifier_resultt::BOTTOM;
  }

  domain.ai_simplify(e, ns);
  if(e.is_true())
  {
    return static_verifier_resultt::TRUE;
  }
  else if(e.is_false())
  {
    return static_verifier_resultt::FALSE;
  }
  else
  {
    return static_verifier_resultt::UNKNOWN;
  }

  UNREACHABLE;
}

/// Runs the analyzer and then prints out the domain
/// \param goto_model: the program analyzed
/// \param ai: the abstract interpreter after it has been run to fix point
/// \param options: the parsed user options
/// \param message_handler: the system message handler
/// \param out: output stream for the printing
/// \return false on success with the domain printed to out
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

  std::vector<static_verifier_resultt> results;

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

      exprt e(i_it->get_condition());

      results.push_back(static_verifier_resultt());
      auto &result = results.back();

      // If there are multiple, distinct histories that reach the same location
      // we can get better results by checking with each individually rather
      // than merging all of them and doing one check.
      const auto trace_set_pointer =
        ai.abstract_traces_before(i_it); // Keep a pointer so refcount > 0
      const auto &trace_set = *trace_set_pointer;

      if(trace_set.size() == 0) // i.e. unreachable
      {
        result.status = static_verifier_resultt::BOTTOM;
        ++pass;
      }
      else if(trace_set.size() == 1)
      {
        auto dp = ai.abstract_state_before(i_it);

        result.status = check_assertion(*dp, e, ns);
        switch(result.status)
        {
        case static_verifier_resultt::BOTTOM:
          ++pass;
          break;
        case static_verifier_resultt::TRUE:
          ++pass;
          break;
        case static_verifier_resultt::FALSE:
          ++fail;
          break;
        case static_verifier_resultt::UNKNOWN:
          ++unknown;
          break;
        default:
          UNREACHABLE;
        }
      }
      else
      {
        // Multiple traces, verify against each one
        std::size_t unreachable_traces = 0;
        std::size_t true_traces = 0;
        std::size_t false_traces = 0;
        std::size_t unknown_traces = 0;

        for(const auto &trace_ptr : trace_set)
        {
          auto dp = ai.abstract_state_before(trace_ptr);

          result.status = check_assertion(*dp, e, ns);
          switch(result.status)
          {
          case static_verifier_resultt::BOTTOM:
            ++unreachable_traces;
            break;
          case static_verifier_resultt::TRUE:
            ++true_traces;
            break;
          case static_verifier_resultt::FALSE:
            ++false_traces;
            break;
          case static_verifier_resultt::UNKNOWN:
            ++unknown_traces;
            break;
          default:
            UNREACHABLE;
          }
        }

        // Join the results
        if(unknown_traces != 0)
        {
          // If any trace is unknown, the final result must be unknown
          result.status = static_verifier_resultt::UNKNOWN;
          ++unknown;
        }
        else
        {
          if(false_traces == 0)
          {
            // Definitely true; the only question is how
            ++pass;
            if(true_traces == 0)
            {
              // Definitely not reachable
              INVARIANT(
                unreachable_traces == trace_set.size(),
                "All traces must not reach the assertion");
              result.status = static_verifier_resultt::BOTTOM;
            }
            else
            {
              // At least one trace (may) reach it.
              // All traces that reach it are safe.
              result.status = static_verifier_resultt::TRUE;
            }
          }
          else
          {
            // At lease one trace (may) reach it and it is false on that trace
            if(true_traces == 0)
            {
              // All traces that (may) reach it are false
              ++fail;
              result.status = static_verifier_resultt::FALSE;
            }
            else
            {
              // The awkward case, there are traces that (may) reach it and
              // some are true, some are false.  It is not entirely fair to say
              // "FAILURE (if reachable)" because it's a bit more complex than
              // that, "FAILURE (if reachable via a particular trace)" would be
              // more accurate summary of what we know at this point.
              // Given that all results of FAILURE from this analysis are
              // caveated with some reachability questions, the following is not
              // entirely unreasonable.
              ++fail;
              result.status = static_verifier_resultt::FALSE;
            }
          }
        }
      }

      result.source_location = i_it->source_location;
      result.function_id = f.first;
    }
  }

  if(options.get_bool_option("json"))
  {
    static_verifier_json(results, m, out);
  }
  else if(options.get_bool_option("xml"))
  {
    static_verifier_xml(results, m, out);
  }
  else if(options.get_bool_option("text"))
  {
    static_verifier_text(results, ns, out);
  }
  else
  {
    static_verifier_console(results, ns, m);
  }

  m.status() << m.bold << "Summary: "
             << pass << " pass, "
             << fail << " fail if reachable, "
             << unknown << " unknown"
             << m.reset << messaget::eom;

  return false;
}
