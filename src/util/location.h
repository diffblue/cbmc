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

  inline const irep_idt &get_property() const
  {
    return get(ID_property);
  }

  inline const irep_idt &get_comment() const
  {
    return get(ID_comment);
  }
  
  inline const irep_idt &get_claim() const
  {
    return get(ID_claim);
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

  inline void set_property(const irep_idt &property)
  {
    set(ID_property, property);
  }

  inline void set_comment(const irep_idt &comment)
  {
    set(ID_comment, comment);
  }
  
  inline void set_claim(const irep_idt &claim)
  {
    set(ID_claim, claim);
  }

};

std::ostream &operator <<(std::ostream &out, const locationt &location);

#endif
