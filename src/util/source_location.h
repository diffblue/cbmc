/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOURCE_LOCATION_H
#define CPROVER_SOURCE_LOCATION_H

#include "irep.h"

class source_locationt:public irept
{
public:
  std::string as_string() const;
  
  inline const irep_idt &get_file() const
  {
    return get(ID_file);
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
  
  inline void set_file(const irep_idt &file)
  {
    set(ID_file, file);
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
  
  inline void set_hide()
  {
    set(ID_hide, true);
  }

  inline bool get_hide() const
  {
    return get_bool(ID_hide);
  }
};

// will go away
typedef source_locationt locationt;

std::ostream &operator <<(std::ostream &, const source_locationt &);

#endif
