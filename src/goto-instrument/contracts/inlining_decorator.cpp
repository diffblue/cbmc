/*******************************************************************\

Module: Utility functions for code contracts.

Author: Remi Delmas, delmasrd@amazon.com

Date: August 2022

\*******************************************************************/

#include "inlining_decorator.h"

inlining_decoratort::inlining_decoratort(message_handlert &_wrapped)
  : wrapped(_wrapped),
    no_body_regex(std::regex(".*no body for function '(.*)'.*")),
    missing_function_regex(
      std::regex(".*missing function '(.*)' is ignored.*")),
    recursive_call_regex(
      std::regex(".*recursion is ignored on call to '(.*)'.*")),
    not_enough_arguments_regex(
      std::regex(".*call to '(.*)': not enough arguments.*"))
{
}

void inlining_decoratort::match_no_body_warning(const std::string &message)
{
  std::smatch sm;
  std::regex_match(message, sm, no_body_regex);
  if(sm.size() == 2)
    no_body_set.insert(sm.str(1));
}

void inlining_decoratort::match_missing_function_warning(
  const std::string &message)
{
  std::smatch sm;
  std::regex_match(message, sm, missing_function_regex);
  if(sm.size() == 2)
    missing_function_set.insert(sm.str(1));
}

void inlining_decoratort::match_recursive_call_warning(
  const std::string &message)
{
  std::smatch sm;
  std::regex_match(message, sm, recursive_call_regex);
  if(sm.size() == 2)
    recursive_call_set.insert(sm.str(1));
}

void inlining_decoratort::match_not_enough_arguments_warning(
  const std::string &message)
{
  std::smatch sm;
  std::regex_match(message, sm, not_enough_arguments_regex);
  if(sm.size() == 2)
    not_enough_arguments_set.insert(sm.str(1));
}

void inlining_decoratort::parse_message(const std::string &message)
{
  match_no_body_warning(message);
  match_missing_function_warning(message);
  match_recursive_call_warning(message);
  match_not_enough_arguments_warning(message);
}

void inlining_decoratort::throw_on_no_body(messaget &log, const int error_code)
{
  if(no_body_set.size() != 0)
  {
    for(auto it : no_body_set)
    {
      log.error() << "No body for '" << it << "' during inlining"
                  << messaget::eom;
    }
    throw error_code;
  }
}

void inlining_decoratort::throw_on_recursive_calls(
  messaget &log,
  const int error_code)
{
  if(recursive_call_set.size() != 0)
  {
    for(auto it : recursive_call_set)
    {
      log.error() << "Recursive call to '" << it << "' during inlining"
                  << messaget::eom;
    }
    throw error_code;
  }
}

void inlining_decoratort::throw_on_missing_function(
  messaget &log,
  const int error_code)
{
  if(missing_function_set.size() != 0)
  {
    for(auto it : missing_function_set)
    {
      log.error() << "Missing function '" << it << "' during inlining"
                  << messaget::eom;
    }
    throw error_code;
  }
}

void inlining_decoratort::throw_on_not_enough_arguments(
  messaget &log,
  const int error_code)
{
  if(not_enough_arguments_set.size() != 0)
  {
    for(auto it : not_enough_arguments_set)
    {
      log.error() << "Not enough arguments for '" << it << "' during inlining"
                  << messaget::eom;
    }
    throw error_code;
  }
}
