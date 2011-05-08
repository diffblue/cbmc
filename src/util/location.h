/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCATION_H
#define CPROVER_LOCATION_H

#include "irep.h"

class locationt:public irept
{
public:
  std::string as_string() const;
  
  const irep_idt &get_file() const
  {
    return get(ID_file);
  }

  const irep_idt &get_line() const
  {
    return get(ID_line);
  }

  const irep_idt &get_column() const
  {
    return get(ID_column);
  }

  const irep_idt &get_function() const
  {
    return get(ID_function);
  }

  const irep_idt &get_property() const
  {
    return get(ID_property);
  }

  const irep_idt &get_comment() const
  {
    return get(ID_comment);
  }

  void set_file(const irep_idt &file)
  {
    set(ID_file, file);
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

  void set_function(const irep_idt &function)
  {
    set(ID_function, function);
  }

  void set_property(const irep_idt &property)
  {
    set(ID_property, property);
  }

  void set_comment(const irep_idt &comment)
  {
    set(ID_comment, comment);
  }

};

std::ostream &operator <<(std::ostream &out, const locationt &location);

#endif
