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
#include <util/json_irep.h>
#include <util/ui_message.h>

/// Output equations from \p equation in plain text format to the given output
/// stream \p out.
/// Each equation is prefixed by a negative index, formatted `{-N}`
static void
show_vcc_plain(messaget::mstreamt &out, const symex_target_equationt &equation)
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

    if(!s_it->comment.empty())
      out << s_it->comment << '\n';

    symex_target_equationt::SSA_stepst::const_iterator p_it =
      equation.SSA_steps.begin();

    // we show everything in case there are threads
    symex_target_equationt::SSA_stepst::const_iterator last_it =
      has_threads ? equation.SSA_steps.end() : s_it;

    for(std::size_t count = 1; p_it != last_it; p_it++)
      if(p_it->is_assume() || p_it->is_assignment() || p_it->is_constraint())
      {
        if(!p_it->ignore && p_it->cond_expr.has_value())
        {
          out << messaget::faint << "{-" << count << "} " << messaget::reset
              << format(p_it->cond_expr->as_expr()) << '\n';

#ifdef DEBUG
          out << "GUARD: " << format(p_it->guard->as_expr()) << '\n';
          out << '\n';
#endif

          count++;
        }
      }

    // Unicode equivalent of "|--------------------------"
    out << messaget::faint << u8"\u251c";
    for(unsigned i = 0; i < 26; i++)
      out << u8"\u2500";
    out << messaget::reset << '\n';

    // split property into multiple disjunts, if applicable
    exprt::operandst disjuncts;

    if(s_it->cond_expr.has_value())
    {
      const exprt cond = s_it->cond_expr->as_expr();
      if(cond.id() == ID_or)
        disjuncts = to_or_expr(cond).operands();
      else
        disjuncts.push_back(cond);
    }

    std::size_t count = 1;
    for(const auto &disjunct : disjuncts)
    {
      out << messaget::faint << '{' << count << "} " << messaget::reset
          << format(disjunct) << '\n';
      count++;
    }

    out << messaget::eom;
  }
}

/// Output equations from \p equation in the JSON format to the given output
/// stream \p out.
/// The format is an array `vccs`, containing fields:
///   - constraints, which is an array containing the constraints which apply
///     to that equation
///   - expression, a string containing the formatted expression
///   - sourceLocation (optional), the corresponding location in the program
///   - comment (optional)
static void
show_vcc_json(std::ostream &out, const symex_target_equationt &equation)
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
        !p_it->ignore && p_it->cond_expr.has_value())
      {
        std::ostringstream string_value;
        string_value << format(p_it->cond_expr->as_expr());
        json_constraints.push_back(json_stringt(string_value.str()));
      }
    }

    if(s_it->cond_expr.has_value())
    {
      std::ostringstream string_value;
      string_value << format(s_it->cond_expr->as_expr());
      object["expression"] = json_stringt(string_value.str());
    }
  }

  out << ",\n" << json_result;
}

void show_vcc(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
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
    show_vcc_json(out, equation);
    break;

  case ui_message_handlert::uit::PLAIN:
    if(have_file)
    {
      msg.status() << "Verification conditions written to file"
                   << messaget::eom;
      stream_message_handlert mout_handler(out);
      messaget mout(mout_handler);
      show_vcc_plain(mout.status(), equation);
    }
    else
    {
      msg.status() << "VERIFICATION CONDITIONS:\n" << messaget::eom;
      show_vcc_plain(msg.status(), equation);
    }
    break;
  }

  if(have_file)
    of.close();
}
