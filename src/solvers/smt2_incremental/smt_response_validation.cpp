// Author: Diffblue Ltd.

/// \file
///
/// Validation of smt response parse trees to produce either a strongly typed
/// `smt_responset` representation, or a set of error messages.
///
/// \note
///
/// Functions named with the prefix `validate_` require the given parse tree to
/// be a particular kind of sub tree. Functions named with the prefix `valid_`
/// are called in places where the exact kind of sub-tree expected is unknown
/// and so the function must determine if the sub-tree is of that type at all,
/// before performing validation of it. These functions will return a
/// `response_or_errort` in the case where the parse tree is of that type or
/// an empty optional otherwise.

#include "smt_response_validation.h"

#include <util/arith_tools.h>
#include <util/mp_arith.h>
#include <util/range.h>

#include <regex>

template <class smtt>
response_or_errort<smtt>::response_or_errort(smtt smt) : smt{std::move(smt)}
{
}

template <class smtt>
response_or_errort<smtt>::response_or_errort(std::string message)
  : messages{std::move(message)}
{
}

template <class smtt>
response_or_errort<smtt>::response_or_errort(std::vector<std::string> messages)
  : messages{std::move(messages)}
{
}

template <class smtt>
const smtt *response_or_errort<smtt>::get_if_valid() const
{
  INVARIANT(
    smt.has_value() == messages.empty(),
    "The response_or_errort class must be in the valid state or error state, "
    "exclusively.");
  return smt.has_value() ? &smt.value() : nullptr;
}

template <class smtt>
const std::vector<std::string> *response_or_errort<smtt>::get_if_error() const
{
  INVARIANT(
    smt.has_value() == messages.empty(),
    "The response_or_errort class must be in the valid state or error state, "
    "exclusively.");
  return smt.has_value() ? nullptr : &messages;
}

template class response_or_errort<smt_responset>;

// Implementation detail of `collect_messages` below.
template <typename argumentt, typename... argumentst>
void collect_messages_impl(
  std::vector<std::string> &collected_messages,
  argumentt &&argument)
{
  if(const auto messages = argument.get_if_error())
  {
    collected_messages.insert(
      collected_messages.end(), messages->cbegin(), messages->end());
  }
}

// Implementation detail of `collect_messages` below.
template <typename argumentt, typename... argumentst>
void collect_messages_impl(
  std::vector<std::string> &collected_messages,
  argumentt &&argument,
  argumentst &&... arguments)
{
  collect_messages_impl(collected_messages, argument);
  collect_messages_impl(collected_messages, arguments...);
}

/// Builds a collection of messages composed all messages in the
/// `response_or_errort` typed arguments in \p arguments. This is a templated
/// function in order to handle `response_or_errort` instances which are
/// specialised differently.
template <typename... argumentst>
std::vector<std::string> collect_messages(argumentst &&... arguments)
{
  std::vector<std::string> collected_messages;
  collect_messages_impl(collected_messages, arguments...);
  return collected_messages;
}

/// \brief Given a class to construct and a set of arguments to its constructor
///   which may include errors, either return the collected errors if there are
///   any or construct the class otherwise.
/// \tparam smt_to_constructt
///   The class to construct.
/// \tparam smt_baset
///   If the class to construct should be upcast to a base class before being
///   stored in the `response_or_errort`, then the base class should be supplied
///   in this parameter. If no upcast is required, then this should be left
///   empty.
/// \tparam argumentst
///   The pack of argument types matching the constructor of
///   `smt_to_constructt`. These must each be packed into an instance of
///   `response_or_errort`.
template <
  typename smt_to_constructt,
  typename smt_baset = smt_to_constructt,
  typename... argumentst>
response_or_errort<smt_baset> validation_propagating(argumentst &&... arguments)
{
  const auto collected_messages = collect_messages(arguments...);
  if(!collected_messages.empty())
    return response_or_errort<smt_baset>(collected_messages);
  else
  {
    return response_or_errort<smt_baset>{
      smt_to_constructt{(*arguments.get_if_valid())...}};
  }
}

/// Produces a human-readable representation of the given \p parse_tree, for use
/// in error messaging.
/// \note This is currently implemented using `pretty`, but this function is
///   used instead of calling `pretty` directly so that will be more straight
///   forward to replace with an implementation specific to our use case which
///   is more easily readable by users of CBMC.
static std::string print_parse_tree(const irept &parse_tree)
{
  return parse_tree.pretty(0, 0);
}

static response_or_errort<irep_idt>
validate_string_literal(const irept &parse_tree)
{
  if(!parse_tree.get_sub().empty())
  {
    return response_or_errort<irep_idt>(
      "Expected string literal, found \"" + print_parse_tree(parse_tree) +
      "\".");
  }
  return response_or_errort<irep_idt>{parse_tree.id()};
}

/// \returns: A response or error in the case where the parse tree appears to be
///   a get-value command. Returns empty otherwise.
/// \note: Because this kind of response does not start with an identifying
///   keyword, it will be considered that the response is intended to be a
///   get-value response if it is composed of a collection of one or more pairs.
static optionalt<response_or_errort<smt_responset>>
valid_smt_error_response(const irept &parse_tree)
{
  // Check if the parse tree looks to be an error response.
  if(!parse_tree.id().empty())
    return {};
  if(parse_tree.get_sub().empty())
    return {};
  if(parse_tree.get_sub().at(0).id() != "error")
    return {};
  // Parse tree is now considered to be an error response and anything
  // unexpected in the parse tree is now considered to be an invalid response.
  if(parse_tree.get_sub().size() == 1)
  {
    return {response_or_errort<smt_responset>{
      "Error response is missing the error message."}};
  }
  if(parse_tree.get_sub().size() > 2)
  {
    return {response_or_errort<smt_responset>{
      "Error response has multiple error messages - \"" +
      print_parse_tree(parse_tree) + "\"."}};
  }
  return validation_propagating<smt_error_responset, smt_responset>(
    validate_string_literal(parse_tree.get_sub()[1]));
}

static bool all_subs_are_pairs(const irept &parse_tree)
{
  return std::all_of(
    parse_tree.get_sub().cbegin(),
    parse_tree.get_sub().cend(),
    [](const irept &sub) { return sub.get_sub().size() == 2; });
}

/// Checks for valid bit vector constants of the form `(_ bv(value) (width))`
/// for example - `(_ bv4 64)`.
static optionalt<smt_termt>
valid_smt_indexed_bit_vector(const irept &parse_tree)
{
  if(parse_tree.get_sub().size() != 3)
    return {};
  if(parse_tree.get_sub().at(0).id() != "_")
    return {};
  const auto value_string = id2string(parse_tree.get_sub().at(1).id());
  std::smatch match_results;
  static const std::regex bv_value_regex{R"(^bv(\d+)$)", std::regex::optimize};
  if(!std::regex_search(value_string, match_results, bv_value_regex))
    return {};
  INVARIANT(
    match_results.size() == 2,
    "Match results should include digits sub-expression if regex is matched.");
  const std::string value_digits = match_results[1];
  const auto value = string2integer(value_digits);
  const auto bit_width_string = id2string(parse_tree.get_sub().at(2).id());
  const auto bit_width =
    numeric_cast_v<std::size_t>(string2integer(bit_width_string));
  if(bit_width == 0)
    return {};
  if(value >= power(mp_integer{2}, bit_width))
    return {};
  return smt_bit_vector_constant_termt{value, bit_width};
}

static optionalt<smt_termt> valid_smt_bool(const irept &parse_tree)
{
  if(!parse_tree.get_sub().empty())
    return {};
  if(parse_tree.id() == ID_true)
    return {smt_bool_literal_termt{true}};
  if(parse_tree.id() == ID_false)
    return {smt_bool_literal_termt{false}};
  return {};
}

static optionalt<smt_termt> valid_smt_binary(const std::string &text)
{
  static const std::regex binary_format{"#b[01]+"};
  if(!std::regex_match(text, binary_format))
    return {};
  const mp_integer value = string2integer({text.begin() + 2, text.end()}, 2);
  // Width is number of bit values minus the "#b" prefix.
  const std::size_t width = text.size() - 2;
  return {smt_bit_vector_constant_termt{value, width}};
}

static optionalt<smt_termt> valid_smt_hex(const std::string &text)
{
  static const std::regex hex_format{"#x[0-9A-Za-z]+"};
  if(!std::regex_match(text, hex_format))
    return {};
  const std::string hex{text.begin() + 2, text.end()};
  // SMT-LIB 2 allows hex characters to be upper or lower case, but they should
  // be upper case for mp_integer.
  const mp_integer value =
    string2integer(make_range(hex).map<std::function<int(int)>>(toupper), 16);
  const std::size_t width = (text.size() - 2) * 4;
  return {smt_bit_vector_constant_termt{value, width}};
}

static optionalt<smt_termt>
valid_smt_bit_vector_constant(const irept &parse_tree)
{
  if(const auto indexed = valid_smt_indexed_bit_vector(parse_tree))
    return *indexed;
  if(!parse_tree.get_sub().empty() || parse_tree.id().empty())
    return {};
  const auto value_string = id2string(parse_tree.id());
  if(const auto smt_binary = valid_smt_binary(value_string))
    return *smt_binary;
  if(const auto smt_hex = valid_smt_hex(value_string))
    return *smt_hex;
  return {};
}

static optionalt<smt_termt> valid_term(const irept &parse_tree)
{
  if(const auto smt_bool = valid_smt_bool(parse_tree))
    return {*smt_bool};
  if(const auto bit_vector_constant = valid_smt_bit_vector_constant(parse_tree))
    return {*bit_vector_constant};
  return {};
}

static response_or_errort<smt_termt> validate_term(const irept &parse_tree)
{
  if(const auto term = valid_term(parse_tree))
    return response_or_errort<smt_termt>{*term};
  return response_or_errort<smt_termt>{"Unrecognised SMT term - \"" +
                                       print_parse_tree(parse_tree) + "\"."};
}

static response_or_errort<smt_termt>
validate_smt_descriptor(const irept &parse_tree, const smt_sortt &sort)
{
  if(const auto term = valid_term(parse_tree))
    return response_or_errort<smt_termt>{*term};
  const auto id = parse_tree.id();
  if(!id.empty())
    return response_or_errort<smt_termt>{smt_identifier_termt{id, sort}};
  return response_or_errort<smt_termt>{
    "Expected descriptor SMT term, found - \"" + print_parse_tree(parse_tree) +
    "\"."};
}

static response_or_errort<smt_get_value_responset::valuation_pairt>
validate_valuation_pair(const irept &pair_parse_tree)
{
  PRECONDITION(pair_parse_tree.get_sub().size() == 2);
  const auto &descriptor = pair_parse_tree.get_sub()[0];
  const auto &value = pair_parse_tree.get_sub()[1];
  const response_or_errort<smt_termt> value_validation = validate_term(value);
  if(const auto value_errors = value_validation.get_if_error())
  {
    return response_or_errort<smt_get_value_responset::valuation_pairt>{
      *value_errors};
  }
  const smt_termt value_term = *value_validation.get_if_valid();
  return validation_propagating<smt_get_value_responset::valuation_pairt>(
    validate_smt_descriptor(descriptor, value_term.get_sort()),
    validate_term(value));
}

/// \returns: A response or error in the case where the parse tree appears to be
///   a get-value command. Returns empty otherwise.
/// \note: Because this kind of response does not start with an identifying
///   keyword, it will be considered that the response is intended to be a
///   get-value response if it is composed of a collection of one or more pairs.
static optionalt<response_or_errort<smt_responset>>
valid_smt_get_value_response(const irept &parse_tree)
{
  // Shape matching for does this look like a get value response?
  if(!parse_tree.id().empty())
    return {};
  if(parse_tree.get_sub().empty())
    return {};
  if(!all_subs_are_pairs(parse_tree))
    return {};
  std::vector<std::string> error_messages;
  std::vector<smt_get_value_responset::valuation_pairt> valuation_pairs;
  for(const auto &pair : parse_tree.get_sub())
  {
    const auto pair_validation_result = validate_valuation_pair(pair);
    if(const auto error = pair_validation_result.get_if_error())
      error_messages.insert(error_messages.end(), error->begin(), error->end());
    if(const auto valid_pair = pair_validation_result.get_if_valid())
      valuation_pairs.push_back(*valid_pair);
  }
  if(!error_messages.empty())
    return {response_or_errort<smt_responset>{std::move(error_messages)}};
  else
  {
    return {response_or_errort<smt_responset>{
      smt_get_value_responset{valuation_pairs}}};
  }
}

response_or_errort<smt_responset> validate_smt_response(const irept &parse_tree)
{
  if(parse_tree.id() == "sat")
    return response_or_errort<smt_responset>{
      smt_check_sat_responset{smt_sat_responset{}}};
  if(parse_tree.id() == "unsat")
    return response_or_errort<smt_responset>{
      smt_check_sat_responset{smt_unsat_responset{}}};
  if(parse_tree.id() == "unknown")
    return response_or_errort<smt_responset>{
      smt_check_sat_responset{smt_unknown_responset{}}};
  if(const auto error_response = valid_smt_error_response(parse_tree))
    return *error_response;
  if(parse_tree.id() == "success")
    return response_or_errort<smt_responset>{smt_success_responset{}};
  if(parse_tree.id() == "unsupported")
    return response_or_errort<smt_responset>{smt_unsupported_responset{}};
  if(const auto get_value_response = valid_smt_get_value_response(parse_tree))
    return *get_value_response;
  return response_or_errort<smt_responset>{"Invalid SMT response \"" +
                                           id2string(parse_tree.id()) + "\""};
}
