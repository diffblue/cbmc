/*******************************************************************\

Module: Range-based reaching definitions analysis (following Field-
        Sensitive Program Dependence Analysis, Litvak et al., FSE 2010)

Author: Michael Tautschnig

Date: February 2013

\*******************************************************************/

#include "static_analysis.h"
#include "local_may_alias.h"

class if_exprt;
class byte_extract_exprt;
class dereference_exprt;

class rd_range_domaint:public domain_baset
{
public:
  rd_range_domaint():
    local_may_alias(0)
  {
  }

  virtual void transform(
      const namespacet &ns,
      locationt from,
      locationt to);

  virtual void output(
      const namespacet &ns,
      std::ostream &out) const;

  // returns true iff there is s.th. new
  bool merge(const rd_range_domaint &other, locationt to);

  void set_may_alias(local_may_aliast *a)
  {
    local_may_alias=a;
  }

protected:
  // each element x represents a range [x.first, x.second.first)
  typedef std::multimap<mp_integer, std::pair<mp_integer, locationt> >
    rangest;
  typedef hash_map_cont<irep_idt, rangest, irep_id_hash> valuest;
  valuest values;

  local_may_aliast * local_may_alias;

  void assign(
    const namespacet &ns,
    locationt from,
    const exprt &lhs,
    const mp_integer &size);
  void assign_if(
    const namespacet &ns,
    locationt from,
    const if_exprt &if_expr,
    const mp_integer &size);
  void assign_dereference(
    const namespacet &ns,
    locationt from,
    const dereference_exprt &deref,
    const mp_integer &size);
  void assign_byte_extract(
    const namespacet &ns,
    locationt from,
    const byte_extract_exprt &be,
    const mp_integer &size);

  void assign(
    const namespacet &ns,
    locationt from,
    const exprt &lhs,
    const mp_integer &range_start,
    const mp_integer &size);

  void kill(
    locationt from,
    const irep_idt &identifier,
    const mp_integer &range_start,
    const mp_integer &size);
  void kill_inf(
    locationt from,
    const irep_idt &identifier,
    const mp_integer &range_start);
  bool gen(
    locationt from,
    const irep_idt &identifier,
    const mp_integer &range_start,
    const mp_integer &size);
};

class reaching_definitions_analysist :
  public static_analysist<rd_range_domaint>
{
public:
  // constructor
  explicit reaching_definitions_analysist(const namespacet &_ns):
    static_analysist<rd_range_domaint>(_ns)
  {
  }

  virtual void initialize(
    const goto_programt &goto_program)
  {
    throw "reaching definitions uses local_may_aliast, cannot be used on goto_programt";
  }

  virtual void initialize(
    const goto_functionst &goto_functions);

protected:
  typedef hash_map_cont<irep_idt, local_may_aliast, irep_id_hash> may_aliasest;
  may_aliasest local_may_aliases;

  virtual void generate_state(locationt l);
};

