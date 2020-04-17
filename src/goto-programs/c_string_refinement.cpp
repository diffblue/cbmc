/*******************************************************************\

Module: C String Refinement

Author: diffblue

\*******************************************************************/

/// \file
/// C String Refinement

#include "c_string_refinement.h"

#include <util/c_types.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/string2int.h>
#include <util/string_expr.h>

#include <goto-programs/goto_model.h>

struct c_string_refinementt : public messaget
{
  c_string_refinementt(
    symbol_tablet &symbol_table,
    message_handlert &message_handler,
    size_t max_nondet_string_length)
    : messaget{message_handler},
      symbol_table(symbol_table),
      ns(symbol_table),
      max_nondet_string_length(max_nondet_string_length)
  {
  }

  void operator()(goto_functionst &goto_functions);

private:
  symbol_tablet &symbol_table;
  namespacet ns;
  size_t max_nondet_string_length;
  size_t symbol_counter = 0;
  const typet string_size_type = size_type();
  const typet string_index_type = index_type();
  const typet string_return_type = signed_int_type();

  auxiliary_symbolt new_aux_string_symbol(
    const std::string &name,
    const typet &type,
    symbol_table_baset &symbol_table);

  refined_string_exprt char_ptr_to_refined_string(
    const exprt &char_ptr,
    const exprt &length_symbol_expr,
    goto_programt &program);

  void do_string_index_of(goto_functiont &string_index_of);
  void do_string_substring(goto_functiont &string_substring);
  void do_string_concat(goto_functiont &string_concat);
};

auxiliary_symbolt c_string_refinementt::new_aux_string_symbol(
  const std::string &name,
  const typet &type,
  symbol_table_baset &symbol_table)
{
  const auto decorated_name =
    std::string{name} + std::to_string(++symbol_counter);
  auxiliary_symbolt new_symbol;
  new_symbol.base_name = decorated_name;
  new_symbol.pretty_name = decorated_name;
  new_symbol.is_static_lifetime = false;
  new_symbol.is_state_var = false;
  new_symbol.mode = ID_C;
  new_symbol.name = decorated_name;
  new_symbol.type = type;
  symbol_table.add(new_symbol);

  return new_symbol;
}

void c_string_refinementt::operator()(goto_functionst &goto_functions)
{
  for(auto it = goto_functions.function_map.begin();
      it != goto_functions.function_map.end();
      it++)
  {
    if(it->first == CPROVER_PREFIX "math_func_string_index_of")
    {
      do_string_index_of(it->second);
    }
    else if(it->first == CPROVER_PREFIX "math_func_string_substring")
    {
      do_string_substring(it->second);
    }
    else if(it->first == CPROVER_PREFIX "math_func_string_concat")
    {
      do_string_concat(it->second);
    }
  }
}

void c_string_refinementt::do_string_concat(goto_functiont &string_concat)
{
  const auto &params = to_code_type(string_concat.type).parameters();
  PRECONDITION(params.size() == 6);
  const auto &res_param = params.at(0);
  const auto &s1_param = params.at(1);
  const auto &s2_param = params.at(2);
  const auto &end_s1_param = params.at(3);
  const auto &start_s2_param = params.at(4);
  const auto &end_s2_param = params.at(5);

  const auto res_param_symbol =
    symbol_exprt{res_param.get_identifier(), res_param.type()};
  const auto s1_param_symbol =
    symbol_exprt{s1_param.get_identifier(), s1_param.type()};
  const auto s2_param_symbol =
    symbol_exprt{s2_param.get_identifier(), s2_param.type()};
  const auto end_s1_param_symbol =
    symbol_exprt{end_s1_param.get_identifier(), end_s1_param.type()};
  const auto start_s2_param_symbol =
    symbol_exprt{start_s2_param.get_identifier(), start_s2_param.type()};
  const auto end_s2_param_symbol =
    symbol_exprt{end_s2_param.get_identifier(), end_s2_param.type()};

  goto_programt new_body;

  const auto res_length_symbol = new_aux_string_symbol(
    "StringConcat::res_length", string_size_type, symbol_table);
  const auto res_length = res_length_symbol.symbol_expr();

  // const auto res_refined_string =
  //   char_ptr_to_refined_string(res_param_symbol, res_length, new_body);
  const auto s1_refined_string = char_ptr_to_refined_string(
    s1_param_symbol,
    typecast_exprt{minus_exprt{end_s1_param_symbol,
                               from_integer(0, end_s1_param_symbol.type())},
                   string_size_type},
    new_body);
  const auto s2_refined_string = char_ptr_to_refined_string(
    s2_param_symbol,
    typecast_exprt{minus_exprt{end_s2_param_symbol, start_s2_param_symbol},
                   string_size_type},
    new_body);

  const auto cprover_string_concat_func_symbol =
    symbol_exprt{ID_cprover_string_concat_func,
                 mathematical_function_typet{{res_length.type(),
                                              res_param_symbol.type(),
                                              // res_refined_string.type(),
                                              s1_refined_string.type(),
                                              s2_refined_string.type(),
                                              start_s2_param_symbol.type(),
                                              end_s2_param_symbol.type()},
                                             string_return_type}};

  const auto apply_concat =
    function_application_exprt{cprover_string_concat_func_symbol,
                               {res_length,
                                // res_refined_string,
                                res_param_symbol,
                                s1_refined_string,
                                s2_refined_string,
                                start_s2_param_symbol,
                                end_s2_param_symbol}};

  const auto return_symbol = new_aux_string_symbol(
    "StringConcat::return", string_return_type, symbol_table);
  const auto return_expr = return_symbol.symbol_expr();
  new_body.add(goto_programt::make_decl(return_expr));
  new_body.add(goto_programt::make_assignment(return_expr, apply_concat));
  new_body.add(goto_programt::make_end_function());

  string_concat.body = std::move(new_body);
}

void c_string_refinementt::do_string_substring(goto_functiont &string_substring)
{
  const auto &params = to_code_type(string_substring.type).parameters();
  PRECONDITION(params.size() == 4);
  const auto &dst_param = params.at(0);
  const auto &src_param = params.at(1);
  const auto &from_param = params.at(2);
  const auto &to_param = params.at(3);

  const auto dst_param_symbol =
    symbol_exprt{dst_param.get_identifier(), dst_param.type()};
  const auto src_param_symbol =
    symbol_exprt{src_param.get_identifier(), src_param.type()};
  const auto from_param_symbol =
    symbol_exprt{from_param.get_identifier(), from_param.type()};
  const auto to_param_symbol =
    symbol_exprt{to_param.get_identifier(), to_param.type()};

  goto_programt new_body;
  const auto dst_length =
    plus_exprt{typecast_exprt{to_param_symbol, string_size_type},
               typecast_exprt{from_param_symbol, string_size_type}};

  // const auto dst_refined_string =
  //   char_ptr_to_refined_string(dst_param_symbol, dst_length, new_body);
  const auto src_length_symbol = new_aux_string_symbol(
    "StringSubstring::src_length", string_size_type, symbol_table);

  const auto src_refined_string = char_ptr_to_refined_string(
    src_param_symbol, src_length_symbol.symbol_expr(), new_body);

  const auto cprover_string_substring_func_symbol =
    symbol_exprt{ID_cprover_string_substring_func,
                 mathematical_function_typet{{dst_length.type(),
                                              // dst_refined_string.type(),
                                              dst_param_symbol.type(),
                                              src_refined_string.type(),
                                              from_param_symbol.type(),
                                              to_param_symbol.type()},
                                             string_return_type}};

  const auto apply_substring =
    function_application_exprt{cprover_string_substring_func_symbol,
                               {dst_length,
                                // dst_refined_string,
                                dst_param_symbol,
                                src_refined_string,
                                from_param_symbol,
                                to_param_symbol}};

  const auto return_symbol = new_aux_string_symbol(
    "StringSubstring::return", string_return_type, symbol_table);
  const auto return_expr = return_symbol.symbol_expr();

  new_body.add(goto_programt::make_decl(return_expr));
  new_body.add(goto_programt::make_assignment(return_expr, apply_substring));
  const auto char_type = dst_param_symbol.type().subtype();
  new_body.add(goto_programt::make_assignment(
    dereference_exprt{
      plus_exprt{dst_param_symbol,
                 minus_exprt{dst_length, from_integer(1, string_size_type)}}},
    from_integer(0, char_type)));
  //  new_body.add(goto_programt::make_return(code_returnt{return_expr}));
  new_body.add(goto_programt::make_end_function());

  string_substring.body = std::move(new_body);
}

void c_string_refinementt::do_string_index_of(goto_functiont &string_index_of)
{
  const auto &params = to_code_type(string_index_of.type).parameters();
  PRECONDITION(params.size() == 3);
  const auto &str_param = params.at(0);
  const auto &length_param = params.at(1);
  const auto &ch_param = params.at(2);
  // const auto refined_string_type =
  //   refined_string_typet{size_type(), to_pointer_type(str_param.type())};
  const auto str_param_symbol =
    symbol_exprt{str_param.get_identifier(), str_param.type()};
  const auto length_param_symbol =
    symbol_exprt{length_param.get_identifier(), length_param.type()};
  const auto ch_param_symbol =
    symbol_exprt{ch_param.get_identifier(), ch_param.type()};
  goto_programt new_body;
  const auto refined_string =
    char_ptr_to_refined_string(str_param_symbol, length_param_symbol, new_body);

  const auto cprover_string_index_of_func_symbol = symbol_exprt{
    ID_cprover_string_index_of_func,
    mathematical_function_typet(
      {refined_string.type(), ch_param_symbol.type()}, string_index_type)};
  const auto apply_index_of = function_application_exprt{
    cprover_string_index_of_func_symbol, {refined_string, ch_param_symbol}};
  const auto return_symbol = new_aux_string_symbol(
    "StringIndexOf::return", string_index_type, symbol_table);
  const auto return_expr = return_symbol.symbol_expr();
  new_body.add(goto_programt::make_decl(return_expr));
  new_body.add(goto_programt::make_assignment(return_expr, apply_index_of));
  new_body.add(goto_programt::make_return(code_returnt{return_expr}));
  new_body.add(goto_programt::make_end_function());

  string_index_of.body = std::move(new_body);
}

/// Helper function to produce the necessary associations related to
/// char-pointers needed for string solver.
refined_string_exprt c_string_refinementt::char_ptr_to_refined_string(
  const exprt &char_ptr,
  const exprt &length_symbol_expr,
  goto_programt &program)
{
  // char *string_content = src;
  const auto content_symbol = new_aux_string_symbol(
    "cprover_string_index_of_func::string_content",
    char_ptr.type(),
    symbol_table);
  const auto content_symbol_expr = content_symbol.symbol_expr();
  program.add(goto_programt::make_decl(content_symbol_expr));
  program.add(goto_programt::make_assignment(content_symbol_expr, char_ptr));

  // char (*nondet_infinite_array_ponter)[\infty];
  const symbolt nondet_infinite_array_pointer = new_aux_string_symbol(
    "cprover_string_index_of_func::nondet_infinite_array_pointer",
    pointer_type(array_typet{char_type(), infinity_exprt(string_size_type)}),
    symbol_table);
  const symbol_exprt nondet_infinite_array_pointer_expr =
    nondet_infinite_array_pointer.symbol_expr();
  program.add(goto_programt::make_decl(nondet_infinite_array_pointer_expr));
  program.add(goto_programt::make_assignment(
    nondet_infinite_array_pointer_expr,
    typecast_exprt{address_of_exprt{char_ptr},
                   nondet_infinite_array_pointer_expr.type()}));

  // cprover_associate_length_to_array_func(nondet_infinite_array_pointer,
  //                                        string_length);
  const auto refined_string_expr = refined_string_exprt{
    length_symbol_expr,
    content_symbol_expr,
    refined_string_typet{length_symbol_expr.type(),
                         to_pointer_type(char_ptr.type())}};
  const symbolt return_array_length = new_aux_string_symbol(
    "cprover_string_index_of_func::return_array_length",
    string_index_type,
    symbol_table);
  dereference_exprt nondet_array_expr{nondet_infinite_array_pointer_expr};
  const auto cprover_associate_length_to_array_func_symbol =
    symbol_exprt{ID_cprover_associate_length_to_array_func,
                 mathematical_function_typet{
                   {nondet_array_expr.type(), length_symbol_expr.type()},
                   return_array_length.type}};
  const auto apply_associate_length_to_array = function_application_exprt{
    cprover_associate_length_to_array_func_symbol,
    {nondet_array_expr, refined_string_expr.length()},
    return_array_length.type};
  const auto return_length_expr = return_array_length.symbol_expr();
  program.add(goto_programt::make_decl(return_length_expr));
  program.add(goto_programt::make_assignment(
    return_length_expr, apply_associate_length_to_array));

  // cprover_associate_array_to_pointer_func(nondet_infinite_array_pointer,
  //                                         src);
  const address_of_exprt array_pointer(
    index_exprt(nondet_array_expr, from_integer(0, string_index_type)));
  program.add(goto_programt::make_assignment(array_pointer, char_ptr));
  const symbolt return_sym_pointer = new_aux_string_symbol(
    "return_array_pointer", string_index_type, symbol_table);
  const auto cprover_associate_array_to_pointer_func_symbol =
    symbol_exprt{ID_cprover_associate_array_to_pointer_func,
                 mathematical_function_typet{
                   {nondet_array_expr.type(), array_pointer.type()},
                   return_sym_pointer.type}};
  const auto apply_associate_pointer_to_array =
    function_application_exprt{cprover_associate_array_to_pointer_func_symbol,
                               {nondet_array_expr, char_ptr}};
  const auto return_pointer_expr = return_sym_pointer.symbol_expr();
  program.add(goto_programt::make_decl(return_pointer_expr));
  program.add(goto_programt::make_assignment(
    return_pointer_expr, apply_associate_pointer_to_array));

  return refined_string_exprt{refined_string_expr.length(), char_ptr};
}

void c_string_refinement(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  const std::string &maybe_max_nondet_string_length_string)
{
  size_t max_nondet_string_length = 1000; // default
  if(!maybe_max_nondet_string_length_string.empty())
  {
    auto maybe_max_nondet_string_length =
      string2optional_size_t(maybe_max_nondet_string_length_string);
    if(!maybe_max_nondet_string_length.has_value())
    {
      throw invalid_command_line_argument_exceptiont{
        "max string length should be a number", "--max-nondet-string-length"};
    }
    max_nondet_string_length = *maybe_max_nondet_string_length;
  }
  auto c_string_refinement = c_string_refinementt{
    goto_model.symbol_table, message_handler, max_nondet_string_length};

  c_string_refinement(goto_model.goto_functions);
}
