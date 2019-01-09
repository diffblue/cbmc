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
    else if(kv.first == "baseName")
      result.base_name = try_get_string(kv.second, "baseName");
    else if(kv.first == "mode")
      result.mode = try_get_string(kv.second, "mode");
    else if(kv.first == "prettyName")
      result.pretty_name = try_get_string(kv.second, "prettyName");
    else if(kv.first == "isType")
      result.is_type = try_get_bool(kv.second, "isType");
    else if(kv.first == "isMacro")
      result.is_macro = try_get_bool(kv.second, "isMacro");
    else if(kv.first == "isExported")
      result.is_exported = try_get_bool(kv.second, "isExported");
    else if(kv.first == "isInput")
      result.is_input = try_get_bool(kv.second, "isInput");
    else if(kv.first == "isOutput")
      result.is_output = try_get_bool(kv.second, "isOutput");
    else if(kv.first == "isStateVar")
      result.is_state_var = try_get_bool(kv.second, "isStateVar");
    else if(kv.first == "isProperty")
      result.is_property = try_get_bool(kv.second, "isProperty");
    else if(kv.first == "isStaticLifetime")
      result.is_static_lifetime = try_get_bool(kv.second, "isStaticLifetime");
    else if(kv.first == "isThreadLocal")
      result.is_thread_local = try_get_bool(kv.second, "isThreadLocal");
    else if(kv.first == "isLvalue")
      result.is_lvalue = try_get_bool(kv.second, "isLvalue");
    else if(kv.first == "isFileLocal")
      result.is_file_local = try_get_bool(kv.second, "isFileLocal");
    else if(kv.first == "isExtern")
      result.is_extern = try_get_bool(kv.second, "isExtern");
    else if(kv.first == "isVolatile")
      result.is_volatile = try_get_bool(kv.second, "isVolatile");
    else if(kv.first == "isParameter")
      result.is_parameter = try_get_bool(kv.second, "isParameter");
    else if(kv.first == "isAuxiliary")
      result.is_auxiliary = try_get_bool(kv.second, "isAuxiliary");
    else if(kv.first == "isWeak")
      result.is_weak = try_get_bool(kv.second, "isWeak");
    else if(kv.first == "prettyType")
    {
    } // ignore
    else if(kv.first == "prettyValue")
    {
    } // ignore
    else
      throw deserialization_exceptiont(
        "symbol_from_json: unexpected key '" + kv.first + "'");
  }

  return result;
}
