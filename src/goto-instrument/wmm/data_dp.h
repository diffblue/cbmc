/*******************************************************************\

Module: data dependencies

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#ifndef DATA_DEP_H
#define DATA_DEP_H

#include <set>

#include <util/location.h>

class abstract_eventt;

/*******************************************************************\
                          data dependencies
\*******************************************************************/

struct datat
{
  irep_idt id;
  locationt loc;
  mutable unsigned eq_class;

  datat(irep_idt _id, locationt _loc, unsigned _eq_class)
  : id(_id), loc(_loc), eq_class(_eq_class)
  {
  }

  datat(irep_idt _id, locationt _loc)
  : id(_id), loc(_loc), eq_class(0)
  {
  }

  bool operator==(const datat& d) const
  {
    return id==d.id && loc==d.loc;
  }

  bool operator<(const datat& d2) const
  {
    return id<d2.id || (id==d2.id && loc<d2.loc);
  }
};

class data_dpt :public std::set<datat>
{
public:
  unsigned class_nb;

  /* add this dependency in the structure */
  void dp_analysis(const abstract_eventt& read, const abstract_eventt& write);
  void dp_analysis(const datat& read, bool local_read, const datat& write,
    bool local_write);

  /* are these two events with a data dependency ? */
  bool dp(const abstract_eventt& e1, const abstract_eventt& e2) const;

  /* routine to maintain partitioning */
  void dp_merge();

  /* printing */
  void print();
};

#endif
