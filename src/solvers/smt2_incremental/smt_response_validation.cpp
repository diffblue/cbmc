// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_response_validation.h>

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

static response_or_errort<irep_idt>
validate_string_literal(const irept &parse_tree)
{
  if(!parse_tree.get_sub().empty())
  {
    return response_or_errort<irep_idt>(
      "Expected string literal, found \"" + parse_tree.pretty(0, 0) + "\".");
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
      "Error response has multiple error messages."}};
  }
  return validation_propagating<smt_error_responset, smt_responset>(
    validate_string_literal(parse_tree.get_sub()[1]));
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
  return response_or_errort<smt_responset>{"Invalid SMT response \"" +
                                           id2string(parse_tree.id()) + "\""};
}
