/*******************************************************************\

Module: Loop unwinding setup

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "unwindset.h"

#include <util/exception_utils.h>
#include <util/message.h>
#include <util/string2int.h>
#include <util/string_utils.h>

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include <fstream>

void unwindsett::parse_unwind(const std::string &unwind)
{
  if(!unwind.empty())
    global_limit = unsafe_string2unsigned(unwind);
}

void unwindsett::parse_unwindset_one_loop(
  std::string val,
  message_handlert &message_handler)
{
  if(val.empty())
    return;

  optionalt<unsigned> thread_nr;
  if(isdigit(val[0]))
  {
    auto c_pos = val.find(':');
    if(c_pos != std::string::npos)
    {
      std::string nr = val.substr(0, c_pos);
      thread_nr = unsafe_string2unsigned(nr);
      val.erase(0, nr.size() + 1);
    }
  }

  auto last_c_pos = val.rfind(':');
  if(last_c_pos != std::string::npos)
  {
    std::string id = val.substr(0, last_c_pos);

    // The loop id can take three forms:
    // 1) Just a function name to limit recursion.
    // 2) F.N where F is a function name and N is a loop number.
    // 3) F.L where F is a function name and L is a label.
    const symbol_tablet &symbol_table = goto_model.get_symbol_table();
    const symbolt *maybe_fn = symbol_table.lookup(id);
    if(maybe_fn && maybe_fn->type.id() == ID_code)
    {
      // ok, recursion limit
    }
    else
    {
      auto last_dot_pos = val.rfind('.');
      if(last_dot_pos == std::string::npos)
      {
        throw invalid_command_line_argument_exceptiont{
          "invalid loop identifier " + id, "unwindset"};
      }

      std::string function_id = id.substr(0, last_dot_pos);
      std::string loop_nr_label = id.substr(last_dot_pos + 1);

      if(loop_nr_label.empty() || !goto_model.can_produce_function(function_id))
      {
        throw invalid_command_line_argument_exceptiont{
          "invalid loop identifier " + id, "unwindset"};
      }

      const goto_functiont &goto_function =
        goto_model.get_goto_function(function_id);
      if(isdigit(loop_nr_label[0]))
      {
        auto nr = string2optional_unsigned(loop_nr_label);
        if(!nr.has_value())
        {
          throw invalid_command_line_argument_exceptiont{
            "invalid loop identifier " + id, "unwindset"};
        }

        bool found = std::any_of(
          goto_function.body.instructions.begin(),
          goto_function.body.instructions.end(),
          [&nr](const goto_programt::instructiont &instruction) {
            return instruction.is_backwards_goto() &&
                   instruction.loop_number == nr;
          });
        if(!found)
        {
          messaget log{message_handler};
          log.warning() << "loop identifier " << id
                        << " provided with unwindset does not match any loop"
                        << messaget::eom;
          return;
        }
      }
      else
      {
        optionalt<unsigned> nr;
        optionalt<source_locationt> location;
        for(const auto &instruction : goto_function.body.instructions)
        {
          if(
            std::find(
              instruction.labels.begin(),
              instruction.labels.end(),
              loop_nr_label) != instruction.labels.end())
          {
            location = instruction.source_location();
          }
          if(
            location.has_value() && instruction.is_backwards_goto() &&
            instruction.source_location() == *location)
          {
            nr = instruction.loop_number;
            break;
          }
        }
        if(!nr.has_value())
        {
          messaget log{message_handler};
          log.warning() << "loop identifier " << id
                        << " provided with unwindset does not match any loop"
                        << messaget::eom;
          return;
        }
        else
          id = function_id + "." + std::to_string(*nr);
      }
    }

    std::string uw_string = val.substr(last_c_pos + 1);

    // the below initialisation makes g++-5 happy
    optionalt<unsigned> uw(0);

    if(uw_string.empty())
      uw = {};
    else
      uw = unsafe_string2unsigned(uw_string);

    if(thread_nr.has_value())
      thread_loop_map[std::pair<irep_idt, unsigned>(id, *thread_nr)] = uw;
    else
      loop_map[id] = uw;
  }
}

void unwindsett::parse_unwindset(
  const std::list<std::string> &unwindset,
  message_handlert &message_handler)
{
  for(auto &element : unwindset)
  {
    std::vector<std::string> unwindset_elements =
      split_string(element, ',', true, true);

    for(auto &element : unwindset_elements)
      parse_unwindset_one_loop(element, message_handler);
  }
}

optionalt<unsigned>
unwindsett::get_limit(const irep_idt &loop_id, unsigned thread_nr) const
{
  // We use the most specific limit we have

  // thread x loop
  auto tl_it =
    thread_loop_map.find(std::pair<irep_idt, unsigned>(loop_id, thread_nr));

  if(tl_it != thread_loop_map.end())
    return tl_it->second;

  // loop
  auto l_it = loop_map.find(loop_id);

  if(l_it != loop_map.end())
    return l_it->second;

  // global, if any
  return global_limit;
}

void unwindsett::parse_unwindset_file(
  const std::string &file_name,
  message_handlert &message_handler)
{
  #ifdef _MSC_VER
  std::ifstream file(widen(file_name));
  #else
  std::ifstream file(file_name);
  #endif

  if(!file)
    throw "cannot open file "+file_name;

  std::stringstream buffer;
  buffer << file.rdbuf();

  std::vector<std::string> unwindset_elements =
    split_string(buffer.str(), ',', true, true);

  for(auto &element : unwindset_elements)
    parse_unwindset_one_loop(element, message_handler);
}
