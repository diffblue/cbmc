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
#include <util/xml_irep.h>

#include <goto-programs/goto_model.h>

#include <analyses/ai.h>

// clang-format off
enum class statust { TRUE, FALSE, BOTTOM, UNKNOWN };
// clang-format on

/// Makes a status message string from a status.
static const char *message(const statust &status)
{
  switch(status)
  {
  case statust::TRUE:
    return "SUCCESS";
  case statust::FALSE:
    return "FAILURE (if reachable)";
  case statust::BOTTOM:
    return "SUCCESS (unreachable)";
  case statust::UNKNOWN:
    return "UNKNOWN";
  }
  UNREACHABLE;
}

struct static_verifier_resultt
{
  statust status;
  source_locationt source_location;
  irep_idt function_id;
  ai_history_baset::trace_sett unknown_histories;
  ai_history_baset::trace_sett false_histories;

  jsont output_json(void) const
  {
    json_arrayt unknown_json;
    for(const auto &trace_ptr : this->unknown_histories)
      unknown_json.push_back(trace_ptr->output_json());

    json_arrayt false_json;
    for(const auto &trace_ptr : this->false_histories)
      false_json.push_back(trace_ptr->output_json());

    return json_objectt{
      {"status", json_stringt{message(this->status)}},
      {"sourceLocation", json(this->source_location)},
      {"unknownHistories", unknown_json},
      {"falseHistories", false_json},
    };
  }

  xmlt output_xml(void) const
  {
    xmlt x("result");

    x.set_attribute("status", message(this->status));

    // DEPRECATED(SINCE(2020, 12, 2, "Remove and use the structured version"));
    // Unstructed partial output of source location is not great...
    x.set_attribute("file", id2string(this->source_location.get_file()));
    x.set_attribute("line", id2string(this->source_location.get_line()));

    // ... this is better
    x.new_element(xml(source_location));

    // ( get_comment is not output as part of xml(source_location) )
    x.set_attribute(
      "description", id2string(this->source_location.get_comment()));

    xmlt &unknown_xml = x.new_element("unknown");
    for(const auto &trace_ptr : this->unknown_histories)
      unknown_xml.new_element(trace_ptr->output_xml());

    xmlt &false_xml = x.new_element("false");
    for(const auto &trace_ptr : this->false_histories)
      false_xml.new_element(trace_ptr->output_xml());

    return x;
  }
};

static statust
check_assertion(const ai_domain_baset &domain, exprt e, const namespacet &ns)
{
  if(domain.is_bottom())
  {
    return statust::BOTTOM;
  }

  domain.ai_simplify(e, ns);
  if(e.is_true())
  {
    return statust::TRUE;
  }
  else if(e.is_false())
  {
    return statust::FALSE;
  }
  else
  {
    return statust::UNKNOWN;
  }

  UNREACHABLE;
}

static static_verifier_resultt check_assertion(
  const ai_baset &ai,
  goto_programt::const_targett assert_location,
  irep_idt function_id,
  const namespacet &ns)
{
  static_verifier_resultt result;

  PRECONDITION(assert_location->is_assert());
  exprt e(assert_location->get_condition());

  // If there are multiple, distinct histories that reach the same location
  // we can get better results by checking with each individually rather
  // than merging all of them and doing one check.
  const auto trace_set_pointer = ai.abstract_traces_before(
    assert_location); // Keep a pointer so refcount > 0
  const auto &trace_set = *trace_set_pointer;

  if(trace_set.size() == 0) // i.e. unreachable
  {
    result.status = statust::BOTTOM;
  }
  else if(trace_set.size() == 1)
  {
    auto dp = ai.abstract_state_before(assert_location);

    result.status = check_assertion(*dp, e, ns);
    if(result.status == statust::FALSE)
    {
      result.false_histories = trace_set;
    }
    else if(result.status == statust::UNKNOWN)
    {
      result.unknown_histories = trace_set;
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
      case statust::BOTTOM:
        ++unreachable_traces;
        break;
      case statust::TRUE:
        ++true_traces;
        break;
      case statust::FALSE:
        ++false_traces;
        result.false_histories.insert(trace_ptr);
        break;
      case statust::UNKNOWN:
        ++unknown_traces;
        result.unknown_histories.insert(trace_ptr);
        break;
      default:
        UNREACHABLE;
      }
    }

    // Join the results
    if(unknown_traces != 0)
    {
      // If any trace is unknown, the final result must be unknown
      result.status = statust::UNKNOWN;
    }
    else
    {
      if(false_traces == 0)
      {
        // Definitely true; the only question is how
        if(true_traces == 0)
        {
          // Definitely not reachable
          INVARIANT(
            unreachable_traces == trace_set.size(),
            "All traces must not reach the assertion");
          result.status = statust::BOTTOM;
        }
        else
        {
          // At least one trace (may) reach it.
          // All traces that reach it are safe.
          result.status = statust::TRUE;
        }
      }
      else
      {
        // At lease one trace (may) reach it and it is false on that trace
        if(true_traces == 0)
        {
          // All traces that (may) reach it are false
          result.status = statust::FALSE;
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
          result.status = statust::FALSE;
        }
      }
    }
  }

  result.source_location = assert_location->source_location;
  result.function_id = function_id;

  return result;
}

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

    auto result = check_assertion(ai, property_location, "unused", ns);

    switch(result.status)
    {
    case statust::TRUE:
      // if the condition simplifies to true the assertion always succeeds
      property_status = property_statust::PASS;
      break;
    case statust::FALSE:
      // if the condition simplifies to false the assertion always fails
      property_status = property_statust::FAIL;
      break;
    case statust::BOTTOM:
      // if the domain state is bottom then the assertion is definitely
      // unreachable
      property_status = property_statust::NOT_REACHABLE;
      break;
    case statust::UNKNOWN:
      // if the condition isn't definitely true, false or unreachable
      // we don't know whether or not it may fail
      property_status = property_statust::UNKNOWN;
      break;
    default:
      UNREACHABLE;
    }
  }
}

static void static_verifier_json(
  const std::vector<static_verifier_resultt> &results,
  messaget &m,
  std::ostream &out)
{
  m.status() << "Writing JSON report" << messaget::eom;
  out << make_range(results)
           .map([](const static_verifier_resultt &result) {
             return result.output_json();
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
    xml_result.new_element(result.output_xml());

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

    out << ": " << message(result.status) << '\n';
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
    case statust::TRUE:
      m.result() << m.green << "SUCCESS" << m.reset;
      break;

    case statust::FALSE:
      m.result() << m.red << "FAILURE" << m.reset << " (if reachable)";
      break;

    case statust::BOTTOM:
      m.result() << m.green << "SUCCESS" << m.reset << " (unreachable)";
      break;

    case statust::UNKNOWN:
      m.result() << m.yellow << "UNKNOWN" << m.reset;
      break;
    }

    m.result() << messaget::eom;
  }

  if(!results.empty())
    m.result() << '\n';
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

      results.push_back(check_assertion(ai, i_it, f.first, ns));

      switch(results.back().status)
      {
      case statust::BOTTOM:
        ++pass;
        break;
      case statust::TRUE:
        ++pass;
        break;
      case statust::FALSE:
        ++fail;
        break;
      case statust::UNKNOWN:
        ++unknown;
        break;
      default:
        UNREACHABLE;
      }
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
