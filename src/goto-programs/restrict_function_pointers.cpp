/*******************************************************************\

Module: Restrict function pointers

Author: Diffblue Ltd.

\*******************************************************************/

#include "restrict_function_pointers.h"

#include <ansi-c/expr2c.h>
#include <json/json_parser.h>
#include <util/expr_iterator.h>
#include <util/string_utils.h>

#include <algorithm>
#include <fstream>
#include <functional>
#include <iostream>

namespace
{
void typecheck_function_pointer_restrictions(
  const goto_modelt &goto_model,
  const function_pointer_restrictionst &restrictions)
{
  for(auto const &restriction : restrictions.restrictions)
  {
    auto const function_pointer_sym =
      goto_model.symbol_table.lookup(restriction.first);
    if(function_pointer_sym == nullptr)
    {
      throw invalid_command_line_argument_exceptiont{
        id2string(restriction.first) + " not found in the symbol table",
        "--restrict-function-pointer"};
    }
    auto const &function_pointer_type = function_pointer_sym->type;
    if(function_pointer_type.id() != ID_pointer)
    {
      throw invalid_command_line_argument_exceptiont{
        "not a function pointer: " + id2string(restriction.first),
        "--restrict-function-pointer"};
    }
    auto const &function_type =
      to_pointer_type(function_pointer_type).subtype();
    if(function_type.id() != ID_code)
    {
      throw invalid_command_line_argument_exceptiont{
        "not a function pointer: " + id2string(restriction.first),
        "--restrict-function-pointer"};
    }
    auto const &ns = namespacet{goto_model.symbol_table};
    for(auto const &function_pointer_target : restriction.second)
    {
      auto const function_pointer_target_sym =
        goto_model.symbol_table.lookup(function_pointer_target);
      if(function_pointer_target_sym == nullptr)
      {
        throw invalid_command_line_argument_exceptiont{
          "symbol not found: " + id2string(function_pointer_target),
          "--restrict-function-pointer"};
      }
      auto const &function_pointer_target_type =
        function_pointer_target_sym->type;
      if(function_type != function_pointer_target_type)
      {
        throw invalid_command_line_argument_exceptiont{
          "type mismatch: `" + id2string(restriction.first) + "' points to `" +
            type2c(function_type, ns) + "', but restriction `" +
            id2string(function_pointer_target) + "' has type `" +
            type2c(function_pointer_target_type, ns) + "'",
          "--restrict-function-pointer"};
      }
    }
  }
}

source_locationt make_function_pointer_restriction_assertion_source_location(
  source_locationt source_location,
  const function_pointer_restrictionst::restrictiont restriction)
{
  std::stringstream comment;

  comment << "dereferenced function pointer at " << restriction.first
          << " must be ";

  if(restriction.second.size() == 1)
  {
    comment << *restriction.second.begin();
  }
  else
  {
    comment << "one of [";

    join_strings(
      comment, restriction.second.begin(), restriction.second.end(), ", ");

    comment << ']';
  }

  source_location.set_comment(comment.str());
  source_location.set_property_class(ID_assertion);

  return source_location;
}

template <typename Handler>
void for_each_function_call(goto_functiont &goto_function, Handler handler)
{
  for_each_instruction_if(
    goto_function,
    [](goto_programt::targett target) { return target->is_function_call(); },
    handler);
}

void handle_call(
  goto_functiont &goto_function,
  goto_modelt &goto_model,
  const function_pointer_restrictionst &restrictions,
  const goto_programt::targett &location)
{
  PRECONDITION(location->is_function_call());

  // for each function call, we check if it is using a symbol we have
  // restrictions for, and if so branch on its value and insert concrete calls
  // to the restriction functions

  // Check if this is calling a function pointer, and if so if it is one
  // we have a restriction for
  const auto &original_function_call = location->get_function_call();

  if(!can_cast_expr<dereference_exprt>(original_function_call.function()))
    return;

  // because we run the label function pointer calls transformation pass before
  // this stage a dereference can only dereference a symbol expression
  auto const &called_function_pointer =
    to_dereference_expr(original_function_call.function()).pointer();
  PRECONDITION(can_cast_expr<symbol_exprt>(called_function_pointer));
  auto const &pointer_symbol = to_symbol_expr(called_function_pointer);
  auto const restriction_iterator =
    restrictions.restrictions.find(pointer_symbol.get_identifier());

  if(restriction_iterator == restrictions.restrictions.end())
    return;

  auto const &restriction = *restriction_iterator;

  // this is intentionally a copy because we're about to change the
  // instruction this iterator points to
  // if we can, we will replace uses of it by a case distinction over
  // given functions the function pointer can point to
  auto const original_function_call_instruction = *location;

  *location = goto_programt::make_assertion(
    false_exprt{},
    make_function_pointer_restriction_assertion_source_location(
      original_function_call_instruction.source_location, restriction));

  auto const assume_false_location = goto_function.body.insert_after(
    location,
    goto_programt::make_assumption(
      false_exprt{}, original_function_call_instruction.source_location));

  // this is mutable because we'll update this at the end of each
  // loop iteration to always point at the start of the branch
  // we created
  auto else_location = location;

  auto const end_if_location = goto_function.body.insert_after(
    assume_false_location, goto_programt::make_skip());

  for(auto const &restriction_target : restriction.second)
  {
    auto new_instruction = original_function_call_instruction;
    // can't use get_function_call because that'll return a const ref
    const symbol_exprt &function_pointer_target_symbol_expr =
      goto_model.symbol_table.lookup_ref(restriction_target).symbol_expr();
    to_code_function_call(new_instruction.code).function() =
      function_pointer_target_symbol_expr;
    auto const goto_end_if_location = goto_function.body.insert_before(
      else_location,
      goto_programt::make_goto(
        end_if_location, original_function_call_instruction.source_location));
    auto const replaced_instruction_location =
      goto_function.body.insert_before(goto_end_if_location, new_instruction);
    else_location = goto_function.body.insert_before(
      replaced_instruction_location,
      goto_programt::make_goto(
        else_location,
        notequal_exprt{pointer_symbol,
                       address_of_exprt{function_pointer_target_symbol_expr}}));
  }
}
} // namespace

void restrict_function_pointers(
  goto_modelt &goto_model,
  const function_pointer_restrictionst &restrictions)
{
  typecheck_function_pointer_restrictions(goto_model, restrictions);

  for(auto &function_item : goto_model.goto_functions.function_map)
  {
    goto_functiont &goto_function = function_item.second;

    for_each_function_call(goto_function, [&](const goto_programt::targett it) {
      handle_call(goto_function, goto_model, restrictions, it);
    });
  }
}

void parse_function_pointer_restriction_options_from_cmdline(
  const cmdlinet &cmdline,
  optionst &options)
{
  options.set_option(
    RESTRICT_FUNCTION_POINTER_OPT,
    cmdline.get_values(RESTRICT_FUNCTION_POINTER_OPT));
  options.set_option(
    RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT,
    cmdline.get_values(RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT));
}

function_pointer_restrictionst::restrictionst
function_pointer_restrictionst::merge_function_pointer_restrictions(
  function_pointer_restrictionst::restrictionst lhs,
  const function_pointer_restrictionst::restrictionst &rhs)
{
  auto &result = lhs;

  for(auto const &restriction : rhs)
  {
    auto emplace_result = result.emplace(restriction.first, restriction.second);
    if(!emplace_result.second)
    {
      for(auto const &target : restriction.second)
      {
        emplace_result.first->second.insert(target);
      }
    }
  }

  return result;
}

function_pointer_restrictionst::restrictionst function_pointer_restrictionst::
  parse_function_pointer_restrictions_from_command_line(
    const std::list<std::string> &restriction_opts)
{
  auto function_pointer_restrictions =
    function_pointer_restrictionst::restrictionst{};

  for(const std::string &restriction_opt : restriction_opts)
  {
    const auto restriction =
      parse_function_pointer_restriction(restriction_opt);

    const bool inserted = function_pointer_restrictions
                            .emplace(restriction.first, restriction.second)
                            .second;

    if(!inserted)
    {
      throw invalid_command_line_argument_exceptiont{
        "function pointer restriction for `" + id2string(restriction.first) +
          "' was specified twice",
        "--" RESTRICT_FUNCTION_POINTER_OPT};
    }
  }

  return function_pointer_restrictions;
}

function_pointer_restrictionst::restrictionst
function_pointer_restrictionst::parse_function_pointer_restrictions_from_file(
  const std::list<std::string> &filenames,
  message_handlert &message_handler)
{
  auto merged_restrictions = function_pointer_restrictionst::restrictionst{};
  for(auto const &filename : filenames)
  {
    auto const restrictions =
      function_pointer_restrictionst::read_from_file(filename, message_handler);

    merged_restrictions = merge_function_pointer_restrictions(
      std::move(merged_restrictions), restrictions.restrictions);
  }

  return merged_restrictions;
}

function_pointer_restrictionst::restrictiont
function_pointer_restrictionst::parse_function_pointer_restriction(
  const std::string &restriction_opt)
{
  // the format for restrictions is <pointer_name>/<target[,more_targets]*>
  // exactly one pointer and at least one target
  auto const pointer_name_end = restriction_opt.find('/');
  auto const restriction_format_message =
    "the format for restrictions is "
    "<pointer_name>/<target[,more_targets]*>";

  if(pointer_name_end == std::string::npos)
  {
    throw invalid_command_line_argument_exceptiont{
      "couldn't find '/' in `" + restriction_opt + "'",
      "--" RESTRICT_FUNCTION_POINTER_OPT,
      restriction_format_message};
  }

  if(pointer_name_end == restriction_opt.size())
  {
    throw invalid_command_line_argument_exceptiont{
      "couldn't find names of targets after '/' in `" + restriction_opt + "'",
      "--" RESTRICT_FUNCTION_POINTER_OPT,
      restriction_format_message};
  }

  if(pointer_name_end == 0)
  {
    throw invalid_command_line_argument_exceptiont{
      "couldn't find target name before '/' in `" + restriction_opt + "'",
      "--" RESTRICT_FUNCTION_POINTER_OPT};
  }

  auto const pointer_name = restriction_opt.substr(0, pointer_name_end);
  auto const target_names_substring =
    restriction_opt.substr(pointer_name_end + 1);
  auto const target_name_strings = split_string(target_names_substring, ',');

  if(target_name_strings.size() == 1 && target_name_strings[0].empty())
  {
    throw invalid_command_line_argument_exceptiont{
      "missing target list for function pointer restriction " + pointer_name,
      "--" RESTRICT_FUNCTION_POINTER_OPT,
      restriction_format_message};
  }

  std::unordered_set<irep_idt> target_names;
  target_names.insert(target_name_strings.begin(), target_name_strings.end());

  for(auto const &target_name : target_names)
  {
    if(target_name == ID_empty_string)
    {
      throw invalid_command_line_argument_exceptiont(
        "leading or trailing comma in restrictions for `" + pointer_name + "'",
        "--" RESTRICT_FUNCTION_POINTER_OPT,
        restriction_format_message);
    }
  }

  return std::make_pair(pointer_name, target_names);
}

function_pointer_restrictionst function_pointer_restrictionst::from_options(
  const optionst &options,
  message_handlert &message_handler)
{
  auto const restriction_opts =
    options.get_list_option(RESTRICT_FUNCTION_POINTER_OPT);
  auto const commandline_restrictions =
    parse_function_pointer_restrictions_from_command_line(restriction_opts);
  auto const file_restrictions = parse_function_pointer_restrictions_from_file(
    options.get_list_option(RESTRICT_FUNCTION_POINTER_FROM_FILE_OPT),
    message_handler);
  return {merge_function_pointer_restrictions(
    std::move(file_restrictions), commandline_restrictions)};
}

function_pointer_restrictionst
function_pointer_restrictionst::from_json(const jsont &json)
{
  function_pointer_restrictionst::restrictionst restrictions;

  if(!json.is_object())
  {
    throw deserialization_exceptiont{"top level item is not an object"};
  }

  for(auto const &restriction : to_json_object(json))
  {
    restrictions.emplace(irep_idt{restriction.first}, [&] {
      if(!restriction.second.is_array())
      {
        throw deserialization_exceptiont{"Value of " + restriction.first +
                                         " is not an array"};
      }
      auto possible_targets = std::unordered_set<irep_idt>{};
      auto const &array = to_json_array(restriction.second);
      std::transform(
        array.begin(),
        array.end(),
        std::inserter(possible_targets, possible_targets.end()),
        [&](const jsont &array_element) {
          if(!array_element.is_string())
          {
            throw deserialization_exceptiont{
              "Value of " + restriction.first +
              "contains a non-string array element"};
          }
          return irep_idt{to_json_string(array_element).value};
        });
      return possible_targets;
    }());
  }

  return function_pointer_restrictionst{restrictions};
}

function_pointer_restrictionst function_pointer_restrictionst::read_from_file(
  const std::string &filename,
  message_handlert &message_handler)
{
  auto inFile = std::ifstream{filename};
  jsont json;

  if(parse_json(inFile, filename, message_handler, json))
  {
    throw deserialization_exceptiont{
      "failed to read function pointer restrictions from " + filename};
  }

  return from_json(json);
}

jsont function_pointer_restrictionst::to_json() const
{
  auto function_pointer_restrictions_json = jsont{};
  auto &restrictions_json_object =
    function_pointer_restrictions_json.make_object();

  for(auto const &restriction : restrictions)
  {
    auto &targets_array =
      restrictions_json_object[id2string(restriction.first)].make_array();
    for(auto const &target : restriction.second)
    {
      targets_array.push_back(json_stringt{target});
    }
  }

  return function_pointer_restrictions_json;
}

void function_pointer_restrictionst::write_to_file(
  const std::string &filename) const
{
  auto function_pointer_restrictions_json = to_json();

  auto outFile = std::ofstream{filename};

  if(!outFile)
  {
    throw system_exceptiont{"cannot open " + filename +
                            " for writing function pointer restrictions"};
  }

  function_pointer_restrictions_json.output(outFile);
}
