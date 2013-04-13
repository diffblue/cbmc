/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_TEMPLATE_MAP_H
#define CPROVER_CPP_TEMPLATE_MAP_H

#include <map>
#include <ostream>

#include <util/expr.h>

#include "cpp_template_type.h"
#include "cpp_template_args.h"

class template_mapt
{
public:
  // this maps template parameters to their instantiated value
  typedef std::map<irep_idt, typet> type_mapt;
  typedef std::map<irep_idt, exprt> expr_mapt;
  type_mapt type_map;
  expr_mapt expr_map;

  void apply(exprt &dest) const;
  void apply(typet &dest) const;

  void swap(template_mapt &template_map)
  {
    type_map.swap(template_map.type_map);
    expr_map.swap(template_map.expr_map);
  }

  exprt lookup(const irep_idt &identifier) const;
  typet lookup_type(const irep_idt &identifier) const;
  exprt lookup_expr(const irep_idt &identifier) const;

  void print(std::ostream &out) const;

  void clear()
  {
    type_map.clear();
    expr_map.clear();
  }
  
  void set(
    const template_parametert &parameter,
    const exprt &value);
  
  void build(
    const template_typet &template_type,
    const cpp_template_args_tct &template_args);

  void build_unassigned(
    const template_typet &template_type);

  cpp_template_args_tct build_template_args(
    const template_typet &template_type) const;
};

class cpp_saved_template_mapt
{
public:
  cpp_saved_template_mapt(template_mapt &map):
    old_map(map), map(map)
  {
  }

  ~cpp_saved_template_mapt()
  {
    #if 0
    std::cout << "RESTORING TEMPLATE MAP\n";
    #endif
    map.swap(old_map);
  }

private:
  template_mapt old_map;
  template_mapt &map;
};

#endif
