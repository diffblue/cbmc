/*******************************************************************\

Module: HTML Traces of GOTO Programs

Author: elizabeth.polgreen@cs.ox.ac.uk

  Date: October 2017

\*******************************************************************/

/// \file
/// HTML traces of GOTO Programs

#include "goto_trace.h"

#include <cassert>
#include <ostream>

#include <util/arith_tools.h>
#include <util/symbol.h>

#include <ansi-c/printf_formatter.h>
#include <langapi/language_util.h>


void output_html_header(std::ostream &out)
{
  out << "<!DOCTYPE html> \n" << "<html> \n" << "<head> \n" << "<style> \n"
      << "button.function_call{ background-color: #eee; color: Black; cursor: pointer; \n"  // NOLINT(*)
      << "padding: 18px; width: 100%; border: double; text-align: left; outline: none; \n" // NOLINT(*)
      << "font-size: 15px; transition: 0.4s; } \n\n"
      << "button.function_call.active, button.fuction_call:hover { background-color: LightGray; }\n"  // NOLINT(*)

      << "div.panel1 { padding: 0 18px; display: none; background-color: AliceBlue; border: 1px solid gray } \n"  // NOLINT(*)
      << "div.panel2 { padding: 0 18px; display: none; background-color: CornSilk; border: 1px solid gray} \n"  // NOLINT(*)
      << "div.property_panel { padding: 0 18px; display: block; background-color: LightGray; border: 1px red} \n"  // NOLINT(*)

      << "</style> \n" << "</head> \n" << "<body> \n"
      << "<h2>CBMC trace</h2> \n";
}

void output_html_footer(std::ostream &out)
{
  out << "<script>\n";

  out
      << "var acc = document.getElementsByClassName(\"function_call\");\n   var i; \n";  // NOLINT(*)

  out << "for (i = 0; i < acc.length; i++) { \n"
      << " acc[i].onclick = function(){ \n"
      << "   this.classList.toggle(\"active\"); \n"
      << "   var panel = this.nextElementSibling; \n"
      << "  if (panel.style.display === \"block\") { \n"
      << "     panel.style.display = \"none\"; \n" << " } else { \n"
      << "   panel.style.display = \"block\"; \n } \n } \n } \n";

  out << " </script> \n"

  << "</body> \n" << "</html> \n";
}


void show_html_state_header(
  std::ostream &out,
  const goto_trace_stept &state,
  const source_locationt &source_location,
  unsigned step_nr)
{
  out << "\n<hr />\n";
  out << "<p><strong><span style=\"color: Indigo;\">";

  if(step_nr==0)
    out << "Initial State";
  else
    out << "State " << step_nr << "</span>";

  out << " " << source_location
      << " thread " << state.thread_nr
      << "</strong>></p>\n";
}


void show_html_goto_trace(
  std::ostream &out,
  const namespacet &ns,
  const goto_tracet &goto_trace)
{
  unsigned prev_step_nr=0;
  bool first_step=true;
  bool use_panel1=true;
  bool use_hex=true; // at some point this will become a cmd line argument
  output_html_header(out);

  for(const auto &step : goto_trace.steps)
  {
    // hide the hidden ones
    if(step.hidden)
      continue;

    switch(step.type)
    {
    case goto_trace_stept::typet::ASSERT:
      if(!step.cond_value)
      {
        out << "\n<hr />\n";
        out << "<div class=\"property_panel\"><p><strong><span style=\"color: Red;\">";  // NOLINT(*)
        out << "Violated property:" << "</span></strong></p>\n";
        if(!step.pc->source_location.is_nil())
          out << "<p><strong>  " << step.pc->source_location << "</strong></p>\n";  // NOLINT(*)
        out << "<p>  " << step.comment << "</p>\n";

        if(step.pc->is_assert())
          out << "<p>  " << from_expr(ns, "", step.pc->guard) << "\n";
        out<<"</p></div>\n";
      }
      break;

    case goto_trace_stept::typet::ASSUME:
      if(!step.cond_value)
      {
        out << "\n<hr />\n";
        out << "<p><strong><span style=\"color: MediumBlue;\">";
        out << "Assumption:" << "</span></strong></p>\n";
        if(!step.pc->source_location.is_nil())
          out << "<p><strong>  " << step.pc->source_location
          << "</strong></p>\n";

        if(step.pc->is_assume())
          out << "<p>  " << from_expr(ns, "", step.pc->guard) << "</p>\n";
      }
      break;

    case goto_trace_stept::typet::LOCATION:
      break;

    case goto_trace_stept::typet::GOTO:
      break;

    case goto_trace_stept::typet::ASSIGNMENT:
      if(step.pc->is_assign() ||
         step.pc->is_return() || // returns have a lhs!
         step.pc->is_function_call() ||
         (step.pc->is_other() && step.lhs_object.is_not_nil()))
      {
        if(prev_step_nr!=step.step_nr || first_step)
        {
          first_step=false;
          prev_step_nr=step.step_nr;
          show_html_state_header(
              out, step, step.pc->source_location, step.step_nr);
          out << "<p><span style=\"color: DarkGray;\">Code:<em> "
              << as_string(ns, *step.pc) << "</em></p>\n";
        }

        // see if the full lhs is something clean
        if(is_index_member_symbol(step.full_lhs))
          trace_value(
            out, ns, step.lhs_object, step.full_lhs,
            step.full_lhs_value, use_hex);
        else
          trace_value(
            out, ns, step.lhs_object, step.lhs_object,
            step.lhs_object_value, use_hex);
      out<<"</span></p>\n";
      }

      break;

    case goto_trace_stept::typet::DECL:
      if(prev_step_nr!=step.step_nr || first_step)
      {
        first_step=false;
        prev_step_nr=step.step_nr;
        show_html_state_header(
            out, step, step.pc->source_location, step.step_nr);
        out << "<p><span style=\"color: DarkGray;\">Code:<em> "
            << as_string(ns, *step.pc) << "</em></p>\n";
      }

      trace_value(
          out, ns, step.lhs_object, step.full_lhs,
          step.full_lhs_value, use_hex);
      out<<"</span></p>\n";
      break;

    case goto_trace_stept::typet::OUTPUT:
      if(step.formatted)
      {
        printf_formattert printf_formatter(ns);
        printf_formatter(id2string(step.format_string), step.io_args);
        printf_formatter.print(out);
      }
      else
      {
        show_html_state_header(
            out, step, step.pc->source_location, step.step_nr);
        out << "<p><span style=\"color: DarkGray;\">Code:<em> "
            << as_string(ns, *step.pc) << "</em></p>\n";

        out << "<p>  OUTPUT " << step.io_id << ":";

        for(std::list<exprt>::const_iterator
            l_it=step.io_args.begin();
            l_it!=step.io_args.end();
            l_it++)
        {
          if(l_it!=step.io_args.begin())
            out << ";";
          out << " " << from_expr(ns, "", *l_it);

          // the hex representation
          out << " (" << trace_value_hex(*l_it, ns) << ")";
        }
      }
      out<<"</span></p>\n";
      break;

    case goto_trace_stept::typet::INPUT:
      show_html_state_header(out, step, step.pc->source_location, step.step_nr);
      out << "<p><span style=\"color: DarkGray;\">Code:<em> "
          << as_string(ns, *step.pc) << "</em></p>\n";
      out << " <p> INPUT " << step.io_id << ":";

      for(std::list<exprt>::const_iterator
          l_it=step.io_args.begin();
          l_it!=step.io_args.end();
          l_it++)
      {
        if(l_it!=step.io_args.begin())
          out << ";";
        out << " " << from_expr(ns, "", *l_it);

        // the binary representation
        out << " (" << trace_value_hex(*l_it, ns) << ")";
      }

      out<<"</span></p>\n";
      break;

    case goto_trace_stept::typet::FUNCTION_CALL:
      out << "\n";
      out << "<button class=\"function_call\">";
      out << "<strong>FUNCTION CALL: </strong>" << as_string(ns, *step.pc);
      if(use_panel1)
      {
        out <<"</button>\n<div class=\"panel1\">\n";
        use_panel1=false;
      }
      else
      {
        out <<"</button>\n<div class=\"panel2\">\n";
        use_panel1=true;
      }

      break;

    case goto_trace_stept::typet::FUNCTION_RETURN:
      out<<"</div>\n";
      break;

    case goto_trace_stept::typet::SPAWN:
    case goto_trace_stept::typet::MEMORY_BARRIER:
    case goto_trace_stept::typet::ATOMIC_BEGIN:
    case goto_trace_stept::typet::ATOMIC_END:
    case goto_trace_stept::typet::DEAD:
      break;

    case goto_trace_stept::typet::CONSTRAINT:
      UNREACHABLE;
      break;

    case goto_trace_stept::typet::SHARED_READ:
    case goto_trace_stept::typet::SHARED_WRITE:
      UNREACHABLE;
      break;

    default:
      UNREACHABLE;
    }
  }
  output_html_footer(out);
}


