/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_SMT2_CONV_H
#define CPROVER_SOLVER_SMT2_CONV_H

#include <sstream>
#include <set>

#include <hash_cont.h>
#include <std_expr.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/pointer_logic.h>

#include "smt2_prop.h"

class smt2_prop_wrappert
{
public:
  smt2_prop_wrappert(
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic,
    bool _core_enabled,
    std::ostream &_out):
    smt2_prop(_benchmark, _notes, _logic, _core_enabled, _out) 
  { }

protected:
  smt2_propt smt2_prop;
};

class typecast_exprt;
class constant_exprt;
class index_exprt;
class member_exprt;

class smt2_convt:
  protected smt2_prop_wrappert,
  public prop_convt
{
public:
  smt2_convt(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic,
    std::ostream &_out):
    smt2_prop_wrappert(_benchmark, _notes, _logic, false, _out),
    prop_convt(_ns, smt2_prop),
    use_FPA_theory(false),
    boolbv_width(_ns),
    pointer_logic(_ns),
    array_index_bits(32),
    num_core_constraints(0)
  { }

  smt2_convt(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic,
    bool _core_enabled,
    std::ostream &_out):
    smt2_prop_wrappert(_benchmark, _notes, _logic, _core_enabled, _out),
    prop_convt(_ns, smt2_prop),
    use_FPA_theory(false),
    boolbv_width(_ns),
    pointer_logic(_ns),
    array_index_bits(32),
    num_core_constraints(0)
  { }

  virtual ~smt2_convt() { }
  virtual resultt dec_solve();

  bool use_FPA_theory;

  // overloading interfaces
  virtual literalt convert(const exprt &expr);
  virtual void set_to(const exprt &expr, bool value);
  virtual exprt get(const exprt &expr) const;
  virtual bool in_core(const exprt &expr);

protected:
  boolbv_widtht boolbv_width;

  // new stuff
  void convert_expr(const exprt &expr);
  void convert_type(const typet &type);
  
  // specific expressions go here
  void convert_byte_update(const exprt &expr);
  void convert_byte_extract(const exprt &expr);
  void convert_typecast(const typecast_exprt &expr);
  void convert_struct(const exprt &expr);
  void convert_union(const exprt &expr);
  void convert_constant(const constant_exprt &expr);
  void convert_relation(const exprt &expr);
  void convert_is_dynamic_object(const exprt &expr);
  void convert_plus(const plus_exprt &expr);
  void convert_minus(const minus_exprt &expr);
  void convert_div(const div_exprt &expr);
  void convert_mult(const mult_exprt &expr);
  void convert_mod(const mod_exprt &expr);
  void convert_index(const index_exprt &expr);
  void convert_member(const member_exprt &expr);
  void convert_overflow(const exprt &expr);
  void convert_with(const exprt &expr);
  void convert_update(const exprt &expr);
  
  std::string convert_identifier(const irep_idt &identifier);
  
  // auxiliary methods
  void find_symbols(const exprt &expr);
  void find_symbols(const typet &type);
  void find_symbols_rec(const typet &type, std::set<irep_idt> &recstack);

  constant_exprt parse_constant(const std::string &s, const typet &type);
  exprt parse_struct(const std::string &s, const typet &type);
  
  // arrays
  typet array_index_type() const;
  void array_index(const exprt &expr);

  // pointers
  pointer_logict pointer_logic;
  void convert_address_of_rec(
    const exprt &expr, const pointer_typet &result_type);

  // keeps track of all symbols
  struct identifiert
  {
    typet type;
    exprt value;
    
    identifiert()
    {
      type.make_nil();
      value.make_nil();
    }
  };
  
  void set_value(
    identifiert &identifier,
    const std::string &v);
  
  typedef hash_map_cont<irep_idt, identifiert, irep_id_hash>
    identifier_mapt;

  identifier_mapt identifier_map;

  typedef std::map<typet, std::string> type_mapt;
  type_mapt type_map;
  
  unsigned array_index_bits;
  
  // for replacing various defined expressions:
  //
  // ID_array_of
  // ID_array
  // ID_string_constant

  typedef std::map<exprt, irep_idt> defined_expressionst;
  defined_expressionst defined_expressions;

  int num_core_constraints;
  std::map<std::string, exprt> core_map;
  std::set<exprt> unsat_core;
};

#endif
