/*******************************************************************\

Module: JSON symbol deserialization

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#include "json_symbol.h"

#include <util/exception_utils.h>
#include <util/expr.h>
#include <util/json_irep.h>
#include <util/source_location.h>
#include <util/type.h>

/// Return string value for a given key if present in the json object.
/// \param in: The json object that is getting fetched as a string.
/// \param key: The key for the json value to be fetched.
/// \return A string value for the corresponding key.
static const std::string &
try_get_string(const jsont &in, const std::string &key)
{
  if(!in.is_string())
    throw deserialization_exceptiont(
      "symbol_from_json: expected string for key '" + key + "'");
  return in.value;
}

/// Return boolean value for a given key if present in the json object.
/// \param in: The json object that is getting fetched as a boolean.
/// \param key: The key for the json value to be fetched.
/// \return A boolean value for the corresponding key.
static bool try_get_bool(const jsont &in, const std::string &key)
{
  if(!(in.is_true() || in.is_false()))
    throw deserialization_exceptiont(
      "symbol_from_json: expected bool for key '" + key + "'");
  return in.is_true();
}

/// Deserialise a json object to a symbolt.
/// \param in: The json object that is getting fetched as an object.
/// \return A symbolt representing the json object.
symbolt symbol_from_json(const jsont &in)
{
  if(!in.is_object())
    throw deserialization_exceptiont("symbol_from_json takes an object");
  symbolt result;
  json_irept json2irep(true);
  for(const auto &kv : to_json_object(in))
  {
    if(kv.first == "type")
    {
      irept irep = json2irep.convert_from_json(kv.second);
      result.type = static_cast<typet &>(irep);
    }
    else if(kv.first == "value")
    {
      irept irep = json2irep.convert_from_json(kv.second);
      result.value = static_cast<exprt &>(irep);
    }
    else if(kv.first == "location")
    {
      irept irep = json2irep.convert_from_json(kv.second);
      result.location = static_cast<source_locationt &>(irep);
    }
    else if(kv.first == "name")
      result.name = try_get_string(kv.second, "name");
    else if(kv.first == "module")
      result.module = try_get_string(kv.second, "module");
    else if(kv.first == "base_name")
      result.base_name = try_get_string(kv.second, "base_name");
    else if(kv.first == "mode")
      result.mode = try_get_string(kv.second, "mode");
    else if(kv.first == "pretty_name")
      result.pretty_name = try_get_string(kv.second, "pretty_name");
    else if(kv.first == "is_type")
      result.is_type = try_get_bool(kv.second, "is_type");
    else if(kv.first == "is_macro")
      result.is_macro = try_get_bool(kv.second, "is_macro");
    else if(kv.first == "is_exported")
      result.is_exported = try_get_bool(kv.second, "is_exported");
    else if(kv.first == "is_input")
      result.is_input = try_get_bool(kv.second, "is_input");
    else if(kv.first == "is_output")
      result.is_output = try_get_bool(kv.second, "is_output");
    else if(kv.first == "is_state_var")
      result.is_state_var = try_get_bool(kv.second, "is_state_var");
    else if(kv.first == "is_property")
      result.is_property = try_get_bool(kv.second, "is_property");
    else if(kv.first == "is_static_lifetime")
      result.is_static_lifetime = try_get_bool(kv.second, "is_static_lifetime");
    else if(kv.first == "is_thread_local")
      result.is_thread_local = try_get_bool(kv.second, "is_thread_local");
    else if(kv.first == "is_lvalue")
      result.is_lvalue = try_get_bool(kv.second, "is_lvalue");
    else if(kv.first == "is_file_local")
      result.is_file_local = try_get_bool(kv.second, "is_file_local");
    else if(kv.first == "is_extern")
      result.is_extern = try_get_bool(kv.second, "is_extern");
    else if(kv.first == "is_volatile")
      result.is_volatile = try_get_bool(kv.second, "is_volatile");
    else if(kv.first == "is_parameter")
      result.is_parameter = try_get_bool(kv.second, "is_parameter");
    else if(kv.first == "is_auxiliary")
      result.is_auxiliary = try_get_bool(kv.second, "is_auxiliary");
    else if(kv.first == "is_weak")
      result.is_weak = try_get_bool(kv.second, "is_weak");
    else
      throw deserialization_exceptiont(
        "symbol_from_json: unexpected key '" + kv.first + "'");
  }

  return result;
}
