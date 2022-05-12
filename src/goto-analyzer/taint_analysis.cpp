/*******************************************************************\

Module: Taint Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Taint Analysis

#include "taint_analysis.h"

#include <iostream>
#include <fstream>

#include <util/invariant.h>
#include <util/json.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/string_constant.h>

#include <goto-programs/class_hierarchy.h>

#include <analyses/custom_bitvector_analysis.h>

#include "taint_parser.h"

class taint_analysist
{
public:
  explicit taint_analysist(message_handlert &message_handler)
    : log(message_handler)
  {
  }

  bool operator()(
    const std::string &taint_file_name,
    const symbol_tablet &,
    goto_functionst &,
    bool show_full,
    const optionalt<std::string> &json_file_name);

protected:
  messaget log;
  taint_parse_treet taint;
  class_hierarchyt class_hierarchy;

  void instrument(const namespacet &, goto_functionst &);
  void instrument(const namespacet &, goto_functionst::goto_functiont &);
};

void taint_analysist::instrument(
  const namespacet &ns,
  goto_functionst &goto_functions)
{
  for(auto &function : goto_functions.function_map)
    instrument(ns, function.second);
}

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

    goto_programt insert_before, insert_after;

    if(instruction.is_function_call())
    {
      const exprt &function = instruction.call_function();

      if(function.id() == ID_symbol)
      {
        const irep_idt &identifier = to_symbol_expr(function).get_identifier();

        std::set<irep_idt> identifiers;

        identifiers.insert(identifier);

        irep_idt class_id = function.get(ID_C_class);
        if(class_id.empty())
        {
        }
        else
        {
          std::string suffix = std::string(
            id2string(identifier), class_id.size(), std::string::npos);

          class_hierarchyt::idst parents =
            class_hierarchy.get_parents_trans(class_id);
          for(const auto &p : parents)
            identifiers.insert(id2string(p) + suffix);
        }

        for(const auto &rule : taint.rules)
        {
          bool match = false;
          for(const auto &i : identifiers)
          {
            if(
              i == rule.function_identifier ||
              has_prefix(
                id2string(i),
                "java::" + id2string(rule.function_identifier) + ":"))
            {
              match = true;
              break;
            }
          }

          if(match)
          {
            log.debug() << "MATCH " << rule.id << " on " << identifier
                        << messaget::eom;

            exprt where = nil_exprt();

            const code_typet &code_type = to_code_type(function.type());

            bool have_this = !code_type.parameters().empty() &&
                             code_type.parameters().front().get_bool(ID_C_this);

            switch(rule.where)
            {
            case taint_parse_treet::rulet::RETURN_VALUE:
            {
              const symbolt &return_value_symbol =
                ns.lookup(id2string(identifier) + "#return_value");
              where = return_value_symbol.symbol_expr();
              break;
            }

            case taint_parse_treet::rulet::PARAMETER:
            {
              unsigned nr =
                have_this ? rule.parameter_number : rule.parameter_number - 1;
              if(instruction.call_arguments().size() > nr)
                where = instruction.call_arguments()[nr];
              break;
            }

            case taint_parse_treet::rulet::THIS:
              if(have_this)
              {
                DATA_INVARIANT(
                  !instruction.call_arguments().empty(),
                  "`this` implies at least one argument in function call");
                where = instruction.call_arguments()[0];
              }
              break;
            }

            switch(rule.kind)
            {
            case taint_parse_treet::rulet::SOURCE:
            {
              codet code_set_may{ID_set_may};
              code_set_may.operands().resize(2);
              code_set_may.op0() = where;
              code_set_may.op1() =
                address_of_exprt(string_constantt(rule.taint));
              insert_after.add(goto_programt::make_other(
                code_set_may, instruction.source_location()));
              break;
            }

            case taint_parse_treet::rulet::SINK:
            {
              binary_predicate_exprt get_may{
                where,
                ID_get_may,
                address_of_exprt(string_constantt(rule.taint))};
              goto_programt::targett t =
                insert_before.add(goto_programt::make_assertion(
                  not_exprt(get_may), instruction.source_location()));
              t->source_location_nonconst().set_property_class(
                "taint rule " + id2string(rule.id));
              t->source_location_nonconst().set_comment(rule.message);
              break;
            }

            case taint_parse_treet::rulet::SANITIZER:
            {
              codet code_clear_may{ID_clear_may};
              code_clear_may.operands().resize(2);
              code_clear_may.op0() = where;
              code_clear_may.op1() =
                address_of_exprt(string_constantt(rule.taint));
              insert_after.add(goto_programt::make_other(
                code_clear_may, instruction.source_location()));
              break;
            }
            }
          }
        }
      }
    }

    if(!insert_before.empty())
    {
      goto_function.body.insert_before_swap(it, insert_before);
      // advance until we get back to the call
      while(!it->is_function_call()) ++it;
    }

    if(!insert_after.empty())
    {
      goto_function.body.destructive_insert(
        std::next(it), insert_after);
    }
  }
}

bool taint_analysist::operator()(
  const std::string &taint_file_name,
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool show_full,
  const optionalt<std::string> &json_file_name)
{
  try
  {
    json_arrayt json_result;
    bool use_json = json_file_name.has_value();

    log.status() << "Reading taint file '" << taint_file_name << "'"
                 << messaget::eom;

    if(taint_parser(taint_file_name, taint, log.get_message_handler()))
    {
      log.error() << "Failed to read taint definition file" << messaget::eom;
      return true;
    }

    log.status() << "Got " << taint.rules.size() << " taint definitions"
                 << messaget::eom;

    log.conditional_output(log.debug(), [this](messaget::mstreamt &mstream) {
      taint.output(mstream);
      mstream << messaget::eom;
    });

    log.status() << "Instrumenting taint" << messaget::eom;

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
      log.status() << "Working from entry point" << messaget::eom;
    }
    else
    {
      log.status() << "No entry point found; "
                   << "we will consider the heads of all functions as reachable"
                   << messaget::eom;

      goto_programt end, gotos, calls;

      end.add(goto_programt::make_end_function());

      for(const auto &gf_entry : goto_functions.function_map)
      {
        if(
          gf_entry.second.body_available() &&
          gf_entry.first != goto_functionst::entry_point())
        {
          const symbolt &symbol = ns.lookup(gf_entry.first);
          const code_function_callt call(symbol.symbol_expr());
          goto_programt::targett t =
            calls.add(goto_programt::make_function_call(call));
          calls.add(
            goto_programt::make_goto(end.instructions.begin(), true_exprt()));
          gotos.add(goto_programt::make_goto(
            t, side_effect_expr_nondett(bool_typet(), symbol.location)));
        }
      }

      goto_functionst::goto_functiont &entry=
        goto_functions.function_map[goto_functionst::entry_point()];

      goto_programt &body=entry.body;

      body.destructive_append(gotos);
      body.destructive_append(calls);
      body.destructive_append(end);

      goto_functions.update();
    }

    log.status() << "Data-flow analysis" << messaget::eom;

    custom_bitvector_analysist custom_bitvector_analysis;
    custom_bitvector_analysis(goto_functions, ns);

    if(show_full)
    {
      custom_bitvector_analysis.output(ns, goto_functions, std::cout);
      return false;
    }

    for(const auto &gf_entry : goto_functions.function_map)
    {
      if(!gf_entry.second.body.has_assertion())
        continue;

      const symbolt &symbol = ns.lookup(gf_entry.first);

      if(gf_entry.first == "__actual_thread_spawn")
        continue;

      bool first=true;

      forall_goto_program_instructions(i_it, gf_entry.second.body)
      {
        if(!i_it->is_assert())
          continue;

        if(!custom_bitvector_domaint::has_get_must_or_may(i_it->condition()))
        {
          continue;
        }

        if(custom_bitvector_analysis[i_it].has_values.is_false())
          continue;

        exprt result = custom_bitvector_analysis.eval(i_it->condition(), i_it);
        if(simplify_expr(std::move(result), ns).is_true())
          continue;

        if(first)
        {
          first=false;
          if(!use_json)
            std::cout << "\n"
                      << "******** Function " << symbol.display_name() << '\n';
        }

        if(use_json)
        {
          json_objectt json{
            {"bugClass",
             json_stringt(i_it->source_location().get_property_class())},
            {"file", json_stringt(i_it->source_location().get_file())},
            {"line",
             json_numbert(id2string(i_it->source_location().get_line()))}};
          json_result.push_back(std::move(json));
        }
        else
        {
          std::cout << i_it->source_location();
          if(!i_it->source_location().get_comment().empty())
            std::cout << ": " << i_it->source_location().get_comment();

          if(!i_it->source_location().get_property_class().empty())
            std::cout << " (" << i_it->source_location().get_property_class()
                      << ")";

          std::cout << '\n';
        }
      }
    }

    if(use_json)
    {
      std::ofstream json_out(json_file_name.value());

      if(!json_out)
      {
        log.error() << "Failed to open json output '" << json_file_name.value()
                    << "'" << messaget::eom;
        return true;
      }

      log.status() << "Analysis result is written to '"
                   << json_file_name.value() << "'" << messaget::eom;

      json_out << json_result << '\n';
    }

    return false;
  }
  catch(const char *error_msg)
  {
    log.error() << error_msg << messaget::eom;
    return true;
  }
  catch(const std::string &error_msg)
  {
    log.error() << error_msg << messaget::eom;
    return true;
  }
  catch(...)
  {
    log.error() << "Caught unexpected error in taint_analysist::operator()"
                << messaget::eom;
    return true;
  }
}

bool taint_analysis(
  goto_modelt &goto_model,
  const std::string &taint_file_name,
  message_handlert &message_handler,
  bool show_full,
  const optionalt<std::string> &json_file_name)
{
  taint_analysist taint_analysis(message_handler);
  return taint_analysis(
    taint_file_name,
    goto_model.symbol_table,
    goto_model.goto_functions,
    show_full,
    json_file_name);
}
