/*******************************************************************\

Module: Assignments to values specified in JSON files

Author: Diffblue Ltd.

\*******************************************************************/

/// \file

#ifndef CPROVER_JAVA_BYTECODE_ASSIGNMENTS_FROM_JSON_H
#define CPROVER_JAVA_BYTECODE_ASSIGNMENTS_FROM_JSON_H

#include "code_with_references.h"
#include <util/std_code.h>

class jsont;
class symbol_table_baset;
class ci_lazy_methods_neededt;

/// Given an expression \p expr representing a Java object or primitive and a
/// JSON representation \p json of the value of a Java object or primitive of a
/// compatible type, adds statements to \p block to assign \p expr to the
/// deterministic value specified by \p json.
/// The expected format of the JSON representation is mostly the same as that
/// of the json-io serialization library (https://github.com/jdereg/json-io) if
/// run with the following options, as of version 4.10.1:
/// - A type name map with identity mappings such as
///   `("java.lang.Boolean", "java.lang.Boolean")` for all primitive wrapper
///   types, java.lang.Class, java.lang.String and java.util.Date. That is, we
///   are not using the json-io default shorthands for those types.
/// - `WRITE_LONGS_AS_STRINGS` should be set to `true` to avoid a loss of
///   precision when representing longs.
///
/// Some examples of json-io representations that may not be obvious include:
/// - The representation of a Java object generally may or may not contain a
///   `"@type"` key. The value corresponding to such a key specifies the runtime
///   type of the object (or the boxed type if the object is primitive). If no
///   `"@type"` key is present, it is assumed that the runtime type is the same
///   as the compile-time type. Most reference-typed objects are represented as
///   JSON objects (i.e. key-value maps) either way, so the `"@type"` key is
///   just an additional key in the map. However, primitive types, arrays and
///   string types without a `"@type"` key are not represented as JSON objects.
///   For example, "untyped" ints are just represented as e.g. 1234, i.e. a JSON
///   number. The "typed" version of this int then becomes
///   `{"@type":"java.lang.Integer","value":1234}`, i.e. a JSON object, with the
///   original ("untyped") JSON number stored in the "value" entry. For arrays,
///   the corresponding key is called "@items", not "value". Typed versions of
///   primitive types are probably not necessary, but json-io will sometimes
///   produce such values, which is why we support both typed and untyped
///   versions.
/// - The way we deal with reference-equal objects is that they all get assigned
///   the same ID, and exactly one of them will have an `{"@id": some_ID}`
///   entry, in addition to its usual representation. All the other objects with
///   this ID are represented simply as `{"@ref": some_ID}`, with no further
///   entries.
///
/// The above rule has the following exceptions:
/// - It seems that strings are always printed in "primitive" representation by
///   json-io, i.e.\ they are always JSON strings, and never JSON objects with
///   a `@type` key. For cases where we don't know that an expression has a
///   string type (e.g.\ if its type is generic and specialized to
///   java.lang.String), we need to sometimes represent strings as JSON objects
///   with a `@type` key. In this case, the content of the string will be the
///   value associated with a `value` key (similarly to StringBuilder in
///   json-io). See \ref get_untyped_string.
/// - json-io does not include the `ordinal` field of enums in its
///   representation, but our algorithm depends on it being present. It may be
///   possible to rewrite parts of it to set the ordinal depending on the order
///   of elements seen in the `$VALUES` array, but it would generally make
///   things more complicated.
///
/// For examples of JSON representations of objects, see the regression tests
/// for this feature in
/// jbmc/regression/jbmc/deterministic_assignments_json.
///
/// Known limitations:
/// - If two reference-equal objects are defined in the same function, they are
///   correctly assigned the same value.
///   However, the case where they are defined in two different functions is not
///   supported. The object that is stored as a `{"@ref":1}` or similar will
///   generally either point to a freshly allocated symbol or an out-of-scope
///   symbol. The `{"@id":1}` (or similar) object may be assigned correctly, or
///   it may point to an out-of-scope symbol. This is because the symbol for the
///   shared value is currently allocated dynamically. To fix this limitation,
///   static allocation would have to be used instead, together with a static
///   boolean to keep track of whether or not the symbol has been allocated
///   already.
/// - The special floating-point values NaN and positive/negative infinity are
///   not supported. Note that in json-io 4.10.1, these are printed as "null".
///   Future versions of json-io will support these values, and this function
///   should be consistent with that if possible.
/// - json-io prints \\uFFFF as a single character, which is not read correctly
///   by the JSON parser.
/// - Not all assignments have source locations, and those that do only link to
///   a function, not a line number.
///
/// For parameter documentation, see \ref object_creation_infot.
code_with_references_listt assign_from_json(
  const exprt &expr,
  const jsont &json,
  const irep_idt &function_id,
  symbol_table_baset &symbol_table,
  optionalt<ci_lazy_methods_neededt> &needed_lazy_methods,
  size_t max_user_array_length,
  std::unordered_map<std::string, object_creation_referencet> &references);

#endif // CPROVER_JAVA_BYTECODE_ASSIGNMENTS_FROM_JSON_H
