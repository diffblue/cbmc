/*******************************************************************\

Module: JSON symbol deserialization

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMBOL_H
#define CPROVER_JSON_SYMTAB_LANGUAGE_JSON_SYMBOL_H

#include <util/symbol.h>

class jsont;

symbolt symbol_from_json(const jsont &);

/// Return string value for a given key if present in the json object.
/// \param in: The json object that is getting fetched as a string.
/// \param key: The key for the json value to be fetched.
/// \return A string value for the corresponding key.
const std::string &try_get_string(const jsont &in, const std::string &key);

/// Return boolean value for a given key if present in the json object.
/// \param in: The json object that is getting fetched as a boolean.
/// \param key: The key for the json value to be fetched.
/// \return A boolean value for the corresponding key.
bool try_get_bool(const jsont &in, const std::string &key);

/// Return a `source_locationt` from the given JSON object.
/// \param json: The json object that represents a source location.
/// \return A source location, unless an exception was thrown before.
source_locationt try_get_source_location(const jsont &json);

#endif
