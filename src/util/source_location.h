/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_SOURCE_LOCATION_H
#define CPROVER_UTIL_SOURCE_LOCATION_H

#include "irep.h"

class source_locationt:public irept
{
public:
  source_locationt()
  {
  }

  inline std::string as_string() const
  {
    return as_string(false);
  }

  inline std::string as_string_with_cwd() const
  {
    return as_string(true);
  }

  inline const irep_idt &get_file() const
  {
    return get(ID_file);
  }

  inline const irep_idt &get_working_directory() const
  {
    return get(ID_working_directory);
  }

  inline const irep_idt &get_line() const
  {
    return get(ID_line);
  }

  inline const irep_idt &get_column() const
  {
    return get(ID_column);
  }

  inline const irep_idt &get_function() const
  {
    return get(ID_function);
  }

  inline const irep_idt &get_property_id() const
  {
    return get(ID_property_id);
  }

  inline const irep_idt &get_property_class() const
  {
    return get(ID_property_class);
  }

  inline const irep_idt &get_comment() const
  {
    return get(ID_comment);
  }

  inline const irep_idt &get_java_bytecode_index() const
  {
    return get(ID_java_bytecode_index);
  }

  inline void set_file(const irep_idt &file)
  {
    set(ID_file, file);
  }

  inline void set_working_directory(const irep_idt &cwd)
  {
    set(ID_working_directory, cwd);
  }

  inline void set_line(const irep_idt &line)
  {
    set(ID_line, line);
  }

  inline void set_line(unsigned line)
  {
    set(ID_line, line);
  }

  inline void set_column(const irep_idt &column)
  {
    set(ID_column, column);
  }

  inline void set_column(unsigned column)
  {
    set(ID_column, column);
  }

  inline void set_function(const irep_idt &function)
  {
    set(ID_function, function);
  }

  inline void set_property_id(const irep_idt &property_id)
  {
    set(ID_property_id, property_id);
  }

  inline void set_property_class(const irep_idt &property_class)
  {
    set(ID_property_class, property_class);
  }

  inline void set_comment(const irep_idt &comment)
  {
    set(ID_comment, comment);
  }

  inline void set_java_bytecode_index(const irep_idt &index)
  {
    set(ID_java_bytecode_index, index);
  }

  inline void set_hide()
  {
    set(ID_hide, true);
  }

  inline bool get_hide() const
  {
    return get_bool(ID_hide);
  }

  inline static const source_locationt &nil()
  {
    return static_cast<const source_locationt &>(get_nil_irep());
  }

protected:
  std::string as_string(bool print_cwd) const;
};

std::ostream &operator <<(std::ostream &, const source_locationt &);

#endif // CPROVER_UTIL_SOURCE_LOCATION_H
