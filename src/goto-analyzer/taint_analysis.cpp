/*******************************************************************\

Module: Taint Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <fstream>

#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/json.h>

#include <ansi-c/string_constant.h>

#include <goto-programs/class_hierarchy.h>

#include <analyses/custom_bitvector_analysis.h>

#include "taint_analysis.h"
#include "taint_parser.h"

/*******************************************************************\

   Class: taint_analysist

 Purpose:

\*******************************************************************/

class taint_analysist:public messaget
{
public:
  taint_analysist()
  {
  }

  bool operator()(
    const std::string &taint_file_name,
    const symbol_tablet &,
    goto_functionst &,
    bool show_full,
    const std::string &json_file_name);

protected:
  taint_parse_treet taint;
  class_hierarchyt class_hierarchy;

  void instrument(const namespacet &, goto_functionst &);
  void instrument(const namespacet &, goto_functionst::goto_functiont &);
};

/*******************************************************************\

Function: taint_analysist::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void taint_analysist::instrument(
  const namespacet &ns,
  goto_functionst &goto_functions)
{
  for(auto & function : goto_functions.function_map)
    instrument(ns, function.second);
}

/*******************************************************************\

Function: taint_analysist::instrument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void taint_analysist::instrument(
  const namespacet &ns,
  goto_functionst::goto_functiont &goto_function)
{
  for(goto_programt::instructionst::iterator
      it=goto_function.body.instructions.begin();
      it!=goto_function.body.instructions.end();
      it++)
  {
    const goto_programt::instructiont &instruction=*it;

    goto_programt tmp;

    switch(instruction.type)
    {
    case FUNCTION_CALL:
      {
        const code_function_callt &function_call=
          to_code_function_call(instruction.code);
        const exprt &function=function_call.function();

        if(function.id()==ID_symbol)
        {
          const irep_idt &identifier=
            to_symbol_expr(function).get_identifier();

          std::set<irep_idt> identifiers;

          identifiers.insert(identifier);

          irep_idt class_id=function.get(ID_C_class);
          if(class_id.empty())
          {

          }
          else
          {
            std::string suffix=
              std::string(id2string(identifier), class_id.size(), std::string::npos);

            class_hierarchyt::idst parents=
              class_hierarchy.get_parents_trans(class_id);
            for(const auto & p : parents)
              identifiers.insert(id2string(p)+suffix);
          }

          for(const auto & rule : taint.rules)
          {
            bool match=false;
            for(const auto & i : identifiers)
              if(i==rule.function_identifier ||
                 has_prefix(id2string(i), "java::"+id2string(rule.function_identifier)+":"))
              {
                match=true;
                break;
              }

            if(match)
            {
              debug() << "MATCH " << rule.id << " on " << identifier << eom;

              exprt where=nil_exprt();

              const code_typet &code_type=to_code_type(function.type());

              bool have_this=
                !code_type.parameters().empty() &&
                code_type.parameters().front().get_bool(ID_C_this);

              switch(rule.where)
              {
              case taint_parse_treet::rulet::RETURN_VALUE:
                {
                  const symbolt &return_value_symbol=
                    ns.lookup(id2string(identifier)+"#return_value");
                  where=return_value_symbol.symbol_expr();
                }
                break;

              case taint_parse_treet::rulet::PARAMETER:
                {
                  unsigned nr=have_this?rule.parameter_number:rule.parameter_number-1;
                  if(function_call.arguments().size()>nr)
                    where=function_call.arguments()[nr];
                }
                break;

              case taint_parse_treet::rulet::THIS:
                if(have_this)
                {
                  assert(!function_call.arguments().empty());
                  where=function_call.arguments()[0];
                }
                break;
              }

              switch(rule.kind)
              {
              case taint_parse_treet::rulet::SOURCE:
                {
                  codet code_set_may("set_may");
                  code_set_may.operands().resize(2);
                  code_set_may.op0()=where;
                  code_set_may.op1()=address_of_exprt(string_constantt(rule.taint));
                  goto_programt::targett t=tmp.add_instruction();
                  t->make_other(code_set_may);
                  t->source_location=instruction.source_location;
                }
                break;

              case taint_parse_treet::rulet::SINK:
                {
                  goto_programt::targett t=tmp.add_instruction();
                  binary_predicate_exprt get_may("get_may");
                  get_may.op0()=where;
                  get_may.op1()=address_of_exprt(string_constantt(rule.taint));
                  t->make_assertion(not_exprt(get_may));
                  t->source_location=instruction.source_location;
                  t->source_location.set_property_class("taint rule "+id2string(rule.id));
                  t->source_location.set_comment(rule.message);
                }
                break;

              case taint_parse_treet::rulet::SANITIZER:
                {
                  codet code_clear_may("clear_may");
                  code_clear_may.operands().resize(2);
                  code_clear_may.op0()=where;
                  code_clear_may.op1()=address_of_exprt(string_constantt(rule.taint));
                  goto_programt::targett t=tmp.add_instruction();
                  t->make_other(code_clear_may);
                  t->source_location=instruction.source_location;
                }
                break;
              }

            }
          }
        }
      }
      break;

    default:;
    }

    if(!tmp.empty())
    {
      goto_programt::targett next=it;
      next++;
      goto_function.body.destructive_insert(next, tmp);
    }
  }
}

/*******************************************************************\

Function: taint_analysist::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool taint_analysist::operator()(
  const std::string &taint_file_name,
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool show_full,
  const std::string &json_file_name)
{
  try
  {
    json_arrayt json_result;
    bool use_json=!json_file_name.empty();

    status() << "Reading taint file `" << taint_file_name
             << "'" << eom;

    if(taint_parser(taint_file_name, taint, get_message_handler()))
    {
      error() << "Failed to read taint definition file" << eom;
      return true;
    }

    status() << "Got " << taint.rules.size()
             << " taint definitions" << eom;

    taint.output(debug());
    debug() << eom;

    status() << "Instrumenting taint" << eom;

    class_hierarchy(symbol_table);

    const namespacet ns(symbol_table);
    instrument(ns, goto_functions);
    goto_functions.update();

    bool have_entry_point=
      goto_functions.function_map.find(goto_functionst::entry_point())!=
      goto_functions.function_map.end();

    // do we have an entry point?
    if(have_entry_point)
    {
      status() << "Working from entry point" << eom;
    }
    else
    {
      status() << "No entry point found; "
                  "we will consider the heads of all functions as reachable" << eom;

      goto_programt end, gotos, calls;

      end.add_instruction(END_FUNCTION);

      forall_goto_functions(f_it, goto_functions)
        if(f_it->second.body_available() &&
           f_it->first!=goto_functionst::entry_point())
        {
          goto_programt::targett t=calls.add_instruction();
          code_function_callt call;
          call.function()=ns.lookup(f_it->first).symbol_expr();
          t->make_function_call(call);
          calls.add_instruction()->make_goto(end.instructions.begin());
          goto_programt::targett g=gotos.add_instruction();
          g->make_goto(t, side_effect_expr_nondett(bool_typet()));
        }

      goto_functionst::goto_functiont &entry=
        goto_functions.function_map[goto_functionst::entry_point()];

      goto_programt &body=entry.body;

      body.destructive_append(gotos);
      body.destructive_append(calls);
      body.destructive_append(end);

      goto_functions.update();
    }

    status() << "Data-flow analysis" << eom;

    custom_bitvector_analysist custom_bitvector_analysis;
    custom_bitvector_analysis(goto_functions, ns);

    if(show_full)
    {
      custom_bitvector_analysis.output(ns, goto_functions, std::cout);
      return false;
    }

    forall_goto_functions(f_it, goto_functions)
    {
      if(!f_it->second.body.has_assertion()) continue;

      const symbolt &symbol=ns.lookup(f_it->first);

      if(f_it->first=="__actual_thread_spawn")
        continue;

      bool first=true;

      forall_goto_program_instructions(i_it, f_it->second.body)
      {
        if(!i_it->is_assert()) continue;
        if(!custom_bitvector_domaint::has_get_must_or_may(i_it->guard))
          continue;

        if(custom_bitvector_analysis[i_it].is_bottom) continue;

        exprt result=custom_bitvector_analysis.eval(i_it->guard, i_it);
        exprt result2=simplify_expr(result, ns);

        if(result2.is_true()) continue;

        if(first)
        {
          first=false;
          if(!use_json)
            std::cout << "\n"
                         "******** Function " << symbol.display_name() << '\n';
        }

        if(use_json)
        {
          json_objectt json;
          json["bug_class"]=json_stringt(id2string(i_it->source_location.get_property_class()));
          json["file"]=json_stringt(id2string(i_it->source_location.get_file()));
          json["line"]=json_numbert(id2string(i_it->source_location.get_line()));
          json_result.array.push_back(json);
        }
        else
        {
          std::cout << i_it->source_location;
          if(!i_it->source_location.get_comment().empty())
            std::cout << ": " << i_it->source_location.get_comment();

          if(!i_it->source_location.get_property_class().empty())
            std::cout << " (" << i_it->source_location.get_property_class() << ")";

          std::cout << '\n';
        }
      }
    }

    if(use_json)
    {
      std::ofstream json_out(json_file_name);

      if(!json_out)
      {
        error() << "Failed to open json output `"
                << json_file_name << "'" << eom;
        return true;
      }

      status() << "Analysis result is written to `"
               << json_file_name << "'" << eom;

      json_out << json_result << '\n';
    }

    return false;
  }
  catch(const char *error_msg)
  {
    error() << error_msg << eom;
    return true;
  }
  catch(const std::string &error_msg)
  {
    error() << error_msg << eom;
    return true;
  }
  catch(...)
  {
    return true;
  }
}

/*******************************************************************\

Function: taint_analysis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool taint_analysis(
  goto_modelt &goto_model,
  const std::string &taint_file_name,
  message_handlert &message_handler,
  bool show_full,
  const std::string &json_file_name)
{
  taint_analysist taint_analysis;
  taint_analysis.set_message_handler(message_handler);
  return taint_analysis(
    taint_file_name, goto_model.symbol_table, goto_model.goto_functions, show_full, json_file_name);
}
