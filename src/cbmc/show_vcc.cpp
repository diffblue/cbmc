/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "bmc.h"

#include <iostream>
#include <fstream>

#include <langapi/mode.h>
#include <langapi/language_util.h>

#include <util/json.h>
#include <util/json_expr.h>

void bmct::show_vcc_plain(std::ostream &out)
{
  out << "\n" << "VERIFICATION CONDITIONS:" << "\n" << "\n";

  bool has_threads=equation.has_threads();

  for(symex_target_equationt::SSA_stepst::iterator
      s_it=equation.SSA_steps.begin();
      s_it!=equation.SSA_steps.end();
      s_it++)
  {
    if(!s_it->is_assert())
      continue;

    if(s_it->source.pc->source_location.is_not_nil())
      out << s_it->source.pc->source_location << "\n";

    if(s_it->comment!="")
      out << s_it->comment << "\n";

    symex_target_equationt::SSA_stepst::const_iterator
      p_it=equation.SSA_steps.begin();

    // we show everything in case there are threads
    symex_target_equationt::SSA_stepst::const_iterator
      last_it=has_threads?equation.SSA_steps.end():s_it;

    for(std::size_t count=1; p_it!=last_it; p_it++)
      if(p_it->is_assume() || p_it->is_assignment() || p_it->is_constraint())
      {
        if(!p_it->ignore)
        {
          std::string string_value=
            from_expr(ns, p_it->source.pc->function, p_it->cond_expr);
          out << "{-" << count << "} " << string_value << "\n";

          #if 0
          languages.from_expr(p_it->guard_expr, string_value);
          out << "GUARD: " << string_value << "\n";
          out << "\n";
          #endif

          count++;
        }
      }

    // Unicode equivalent of "|--------------------------"
    out << u8"\u251c";
    for(unsigned i=0; i<26; i++) out << u8"\u2500";
    out << '\n';

    std::string string_value=
      from_expr(ns, s_it->source.pc->function, s_it->cond_expr);
    out << "{" << 1 << "} " << string_value << "\n";

    out << "\n";
  }
}

void bmct::show_vcc_json(std::ostream &out)
{
  json_objectt json_result;

  json_arrayt &json_vccs=json_result["vccs"].make_array();

  bool has_threads=equation.has_threads();

  for(symex_target_equationt::SSA_stepst::iterator
      s_it=equation.SSA_steps.begin();
      s_it!=equation.SSA_steps.end();
      s_it++)
  {
    if(!s_it->is_assert())
      continue;

    // vcc object
    json_objectt &object=json_vccs.push_back(jsont()).make_object();

    const source_locationt &source_location=s_it->source.pc->source_location;
    if(source_location.is_not_nil())
      object["sourceLocation"]=json(source_location);

    const std::string &s=s_it->comment;
    if(!s.empty())
      object["comment"]=json_stringt(s);

    // we show everything in case there are threads
    symex_target_equationt::SSA_stepst::const_iterator
      last_it=has_threads?equation.SSA_steps.end():s_it;

    json_arrayt &json_constraints=object["constraints"].make_array();

    for(symex_target_equationt::SSA_stepst::const_iterator p_it
          =equation.SSA_steps.begin();
        p_it!=last_it; p_it++)
    {
      if((p_it->is_assume() ||
         p_it->is_assignment() ||
         p_it->is_constraint()) &&
         !p_it->ignore)
      {
        std::string string_value=
          from_expr(ns, p_it->source.pc->function, p_it->cond_expr);
        json_constraints.push_back(json_stringt(string_value));
      }
    }

    std::string string_value=
      from_expr(ns, s_it->source.pc->function, s_it->cond_expr);
    object["expression"]=json_stringt(string_value);
  }

  out << ",\n" << json_result;
}

void bmct::show_vcc()
{
  const std::string &filename=options.get_option("outfile");
  bool have_file=!filename.empty() && filename!="-";

  std::ofstream of;

  if(have_file)
  {
    of.open(filename);
    if(!of)
      throw "failed to open file "+filename;
  }

  std::ostream &out=have_file?of:std::cout;

  switch(ui)
  {
  case ui_message_handlert::uit::XML_UI:
    error() << "XML UI not supported" << eom;
    return;

  case ui_message_handlert::uit::JSON_UI:
    show_vcc_json(out);
    break;

  case ui_message_handlert::uit::PLAIN:
    show_vcc_plain(out);
    break;
  }

  if(have_file)
    of.close();
}
