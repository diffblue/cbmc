/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_TYPECAST_H
#define CPROVER_CPP_TYPECAST_H

#include <ansi-c/c_typecast.h>

class cpp_typecheckt;

class cpp_typecastt:public c_typecastt
{
public:
  cpp_typecastt(cpp_typecheckt &cpp_typecheck);

  virtual void implicit_typecast(
    exprt &expr,
    const typet &type);

  virtual void implicit_typecast_arithmetic(
    exprt &expr);

  virtual void implicit_typecast_arithmetic(
    exprt &expr1,
    exprt &expr2);

protected:
  virtual void implicit_typecast_followed(
    exprt &expr,
    const typet &src_type,
    const typet &dest_type);

  void get_bases(
    const irep_idt &identifier,
    std::map<irep_idt, unsigned> &base_count);

public:
  void check_qualifiers(
    const typet &from,
    const typet &to);

  bool subtype_typecast(
    const typet &from,
    const typet &to,
    std::string& err);

  bool integral_conversion(
      const typet &src_type,
      const typet &dest_type);

  exprt subtype_offset(
      const struct_typet &from,
      const struct_typet &to);

  void make_ptr_typecast(
      exprt &expr,
      const typet & src_type,
      const typet & dest_type);

  cpp_typecheckt &cpp_typecheck;
};

#endif
