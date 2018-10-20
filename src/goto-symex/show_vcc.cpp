/*******************************************************************\

Module: Output of the verification conditions (VCCs)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Output of the verification conditions (VCCs)

#include "show_vcc.h"
#include "symex_target_equation.h"

#include <fstream>
#include <iostream>
#include <sstream>

#include <goto-symex/symex_target_equation.h>

#include <util/exception_utils.h>
#include <util/format_expr.h>
#include <util/json.h>
#include <util/json_expr.h>
#include <util/ui_message.h>

void show_vcc_plain(
  std::ostream &out,
  const namespacet &ns,
  const symex_target_equationt &equation)
{
  bool has_threads = equation.has_threads();
  bool first = true;

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        equation.SSA_steps.begin();
      s_it != equation.SSA_steps.end();
      s_it++)
  {
    if(!s_it->is_assert())
      continue;

    if(first)
      first = false;
    else
      out << '\n';

    if(s_it->source.pc->source_location.is_not_nil())
      out << s_it->source.pc->source_location << '\n';

    if(s_it->comment != "")
      out << s_it->comment << '\n';

    symex_target_equationt::SSA_stepst::const_iterator p_it =
      equation.SSA_steps.begin();

    // we show everything in case there are threads
    symex_target_equationt::SSA_stepst::const_iterator last_it =
      has_threads ? equation.SSA_steps.end() : s_it;

    for(std::size_t count = 1; p_it != last_it; p_it++)
      if(p_it->is_assume() || p_it->is_assignment() || p_it->is_constraint())
      {
        if(!p_it->ignore)
        {
          out << "{-" << count << "} " << format(p_it->cond_expr) << '\n';

#ifdef DEBUG
          out << "GUARD: " << format(p_it->guard) << '\n';
          out << '\n';
#endif

          count++;
        }
      }

    // Unicode equivalent of "|--------------------------"
    out << u8"\u251c";
    for(unsigned i = 0; i < 26; i++)
      out << u8"\u2500";
    out << '\n';

    // split property into multiple disjunts, if applicable
    exprt::operandst disjuncts;

    if(s_it->cond_expr.id() == ID_or)
      disjuncts = to_or_expr(s_it->cond_expr).operands();
    else
      disjuncts.push_back(s_it->cond_expr);

    std::size_t count = 1;
    for(const auto &disjunct : disjuncts)
    {
      out << '{' << count << "} " << format(disjunct) << '\n';
      count++;
    }
  }
}

void show_vcc_json(
  std::ostream &out,
  const namespacet &ns,
  const symex_target_equationt &equation)
{
  json_objectt json_result;

  json_arrayt &json_vccs = json_result["vccs"].make_array();

  bool has_threads = equation.has_threads();

  for(symex_target_equationt::SSA_stepst::const_iterator s_it =
        equation.SSA_steps.begin();
      s_it != equation.SSA_steps.end();
      s_it++)
  {
    if(!s_it->is_assert())
      continue;

    // vcc object
    json_objectt &object = json_vccs.push_back(jsont()).make_object();

    const source_locationt &source_location = s_it->source.pc->source_location;
    if(source_location.is_not_nil())
      object["sourceLocation"] = json(source_location);

    const std::string &s = s_it->comment;
    if(!s.empty())
      object["comment"] = json_stringt(s);

    // we show everything in case there are threads
    symex_target_equationt::SSA_stepst::const_iterator last_it =
      has_threads ? equation.SSA_steps.end() : s_it;

    json_arrayt &json_constraints = object["constraints"].make_array();

    for(symex_target_equationt::SSA_stepst::const_iterator p_it =
          equation.SSA_steps.begin();
        p_it != last_it;
        p_it++)
    {
      if(
        (p_it->is_assume() || p_it->is_assignment() || p_it->is_constraint()) &&
        !p_it->ignore)
      {
        std::ostringstream string_value;
        string_value << format(p_it->cond_expr);
        json_constraints.push_back(json_stringt(string_value.str()));
      }
    }

    std::ostringstream string_value;
    string_value << format(s_it->cond_expr);
    object["expression"] = json_stringt(string_value.str());
  }

  out << ",\n" << json_result;
}

void show_vcc(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  const namespacet &ns,
  const symex_target_equationt &equation)
{
  messaget msg(ui_message_handler);

  const std::string &filename = options.get_option("outfile");
  bool have_file = !filename.empty() && filename != "-";

  std::ofstream of;

  if(have_file)
  {
    of.open(filename);
    if(!of)
      throw invalid_command_line_argument_exceptiont(
        "failed to open output file: " + filename, "--outfile");
  }

  std::ostream &out = have_file ? of : std::cout;

  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::XML_UI:
    msg.error() << "XML UI not supported" << messaget::eom;
    return;

  case ui_message_handlert::uit::JSON_UI:
    show_vcc_json(out, ns, equation);
    break;

  case ui_message_handlert::uit::PLAIN:
    msg.status() << "VERIFICATION CONDITIONS:\n" << messaget::eom;
    if(have_file)
      show_vcc_plain(out, ns, equation);
    else
    {
      show_vcc_plain(msg.status(), ns, equation);
      msg.status() << messaget::eom;
    }
    break;
  }

  if(have_file)
    of.close();
}
