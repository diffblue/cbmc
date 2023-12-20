/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SOURCE_LOCATION_H
#define CPROVER_UTIL_SOURCE_LOCATION_H

#include "deprecate.h"
#include "irep.h"

#include <optional>
#include <string>

class source_locationt:public irept
{
public:
  source_locationt()
  {
  }

  std::string as_string() const
  {
    return as_string(false);
  }

  std::string as_string_with_cwd() const
  {
    return as_string(true);
  }

  const irep_idt &get_file() const
  {
    return get(ID_file);
  }

  const irep_idt &get_working_directory() const
  {
    return get(ID_working_directory);
  }

  const irep_idt &get_line() const
  {
    return get(ID_line);
  }

  const irep_idt &get_column() const
  {
    return get(ID_column);
  }

  // This method is problematic for the following reasons:
  // 1) There is ambiguity whether
  //    the returned string is an identifier or human-readable.
  // 2) Furthermore, the linker renames functions, and is unable
  //    to adjust all source locations.
  // 3) The name of the function is not strictly a source location.
  // It will be removed.
  // DEPRECATED(SINCE(2022, 10, 13, "use identifier of containing function"))
  const irep_idt &get_function() const
  {
    return get(ID_function);
  }

  const irep_idt &get_property_id() const
  {
    return get(ID_property_id);
  }

  const irep_idt &get_property_class() const
  {
    return get(ID_property_class);
  }

  const irep_idt &get_comment() const
  {
    return get(ID_comment);
  }

  const irep_idt &get_case_number() const
  {
    return get(ID_switch_case_number);
  }

  const irep_idt &get_java_bytecode_index() const
  {
    return get(ID_java_bytecode_index);
  }

  const irept &get_basic_block_source_lines() const
  {
    return find(ID_basic_block_source_lines);
  }

  void set_file(const irep_idt &file)
  {
    set(ID_file, file);
  }

  void set_working_directory(const irep_idt &cwd)
  {
    set(ID_working_directory, cwd);
  }

  void set_line(const irep_idt &line)
  {
    set(ID_line, line);
  }

  void set_line(unsigned line)
  {
    set(ID_line, line);
  }

  void set_column(const irep_idt &column)
  {
    set(ID_column, column);
  }

  void set_column(unsigned column)
  {
    set(ID_column, column);
  }

  // DEPRECATED(SINCE(2022, 10, 13, "use identifier of containing function"))
  void set_function(const irep_idt &function)
  {
    set(ID_function, function);
  }

  void set_property_id(const irep_idt &property_id)
  {
    set(ID_property_id, property_id);
  }

  void set_property_class(const irep_idt &property_class)
  {
    set(ID_property_class, property_class);
  }

  void set_comment(const irep_idt &comment)
  {
    set(ID_comment, comment);
  }

  // for switch case number
  void set_case_number(const irep_idt &number)
  {
    set(ID_switch_case_number, number);
  }

  void set_java_bytecode_index(const irep_idt &index)
  {
    set(ID_java_bytecode_index, index);
  }

  void set_basic_block_source_lines(irept source_lines)
  {
    add(ID_basic_block_source_lines, std::move(source_lines));
  }

  void set_hide()
  {
    set(ID_hide, true);
  }

  bool get_hide() const
  {
    return get_bool(ID_hide);
  }

  static bool is_built_in(const std::string &s);

  bool is_built_in() const
  {
    return is_built_in(id2string(get_file()));
  }

  /// Set all unset source-location fields in this object to their values in
  /// 'from'. Leave set fields in this object alone.
  void merge(const source_locationt &from);

  static const source_locationt &nil()
  {
    return static_cast<const source_locationt &>(get_nil_irep());
  }

  std::optional<std::string> full_path() const;

  void add_pragma(const irep_idt &pragma)
  {
    add(ID_pragma).add(pragma);
  }

  const irept::named_subt &get_pragmas() const
  {
    return find(ID_pragma).get_named_sub();
  }

protected:
  std::string as_string(bool print_cwd) const;
};

std::ostream &operator <<(std::ostream &, const source_locationt &);

template <>
struct diagnostics_helpert<source_locationt>
{
  static std::string
  diagnostics_as_string(const source_locationt &source_location)
  {
    return "source location: " + source_location.as_string();
  }
};

#endif // CPROVER_UTIL_SOURCE_LOCATION_H
