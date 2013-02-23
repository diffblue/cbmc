/*******************************************************************\

Module: SMT Version 1 Backend

Author: Daniel Kroening, kroening@kroening.com
Revision: Roberto Bruttomesso, roberto.bruttomesso@unisi.ch

\*******************************************************************/

#ifndef CPROVER_SOLVER_SMT_CONV_H
#define CPROVER_SOLVER_SMT_CONV_H

#include <sstream>
#include <set>

#include <hash_cont.h>
#include <std_expr.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/pointer_logic.h>
#include <solvers/flattening/boolbv_width.h>

#include "smt1_prop.h"

class smt1_prop_wrappert
{
public:
  smt1_prop_wrappert(
    const std::string &_benchmark,
    const std::string &_source,
    const std::string &_logic,
    std::ostream &_out):
    smt1_prop(_benchmark, _source, _logic, _out) 
  { }

protected:
  smt1_propt smt1_prop;
};

class typecast_exprt;
class constant_exprt;
class index_exprt;
class member_exprt;

class smt1_convt:
  protected smt1_prop_wrappert,
  public prop_convt
{
public:
  smt1_convt(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_source,
    const std::string &_logic,    
    std::ostream &_out):
    smt1_prop_wrappert(_benchmark, _source, _logic, _out),
    prop_convt(_ns, smt1_prop),
    boolbv_width(_ns),
    pointer_logic(_ns),
    array_index_bits(32)
  { }

  virtual ~smt1_convt() { }
  virtual resultt dec_solve();

  // overloading interfaces
  virtual literalt convert(const exprt &expr);
  virtual void set_to(const exprt &expr, bool value);
  virtual exprt get(const exprt &expr) const;

protected:
  boolbv_widtht boolbv_width;

  // new stuff
  void convert_expr(const exprt &expr, bool bool_as_bv);
  void convert_type(const typet &type);
  
  // specific expressions go here
  void convert_byte_update(const exprt &expr, bool bool_as_bv);
  void convert_byte_extract(const exprt &expr, bool bool_as_bv);
  void convert_typecast(const typecast_exprt &expr, bool bool_as_bv);
  void convert_struct(const exprt &expr);
  void convert_union(const exprt &expr);
  void convert_constant(const constant_exprt &expr, bool bool_as_bv);
  void convert_relation(const exprt &expr, bool bool_as_bv);
  void convert_is_dynamic_object(const exprt &expr, bool bool_as_bv);
  void convert_plus(const plus_exprt &expr);
  void convert_minus(const minus_exprt &expr);
  void convert_div(const div_exprt &expr);
  void convert_mult(const mult_exprt &expr);
  void convert_mod(const mod_exprt &expr);
  void convert_index(const index_exprt &expr, bool bool_as_bv);
  void convert_member(const member_exprt &expr, bool bool_as_bv);
  void convert_overflow(const exprt &expr);
  void convert_with(const exprt &expr);
  
  std::string convert_identifier(const irep_idt &identifier);
  
  // auxiliary methods
  std::set<irep_idt> quantified_symbols;
  void find_symbols(const exprt &expr);
  void find_symbols(const typet &type);
  void find_symbols_rec(const typet &type, std::set<irep_idt> &recstack);
  void flatten_array(const exprt &op);
  
  // booleans vs. bit-vector[1]
  void from_bv_begin(const typet &type, bool bool_as_bv);
  void from_bv_end(const typet &type, bool bool_as_bv);
  void from_bool_begin(const typet &type, bool bool_as_bv);
  void from_bool_end(const typet &type, bool bool_as_bv);
  
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
    const std::string &index,
    const std::string &value)
  {
    exprt tmp=ce_value(identifier.type, index, value, false);
    if(tmp.id()=="array-list" && identifier.value.id()=="array-list")
    {
      forall_operands(it, tmp)
        identifier.value.copy_to_operands(*it);
    }
    else
      identifier.value=tmp;
  }
  
  typedef hash_map_cont<irep_idt, identifiert, irep_id_hash>
    identifier_mapt;

  identifier_mapt identifier_map;
  
  unsigned array_index_bits;
  
  // for replacing 'array_of' expressions
  typedef std::map<exprt, irep_idt> array_of_mapt;
  array_of_mapt array_of_map;
  
  // for replacing 'array' expressions
  typedef std::map<exprt, irep_idt> array_expr_mapt;
  array_expr_mapt array_expr_map;
  
  // for replacing string constants
  typedef std::map<exprt, exprt> string2array_mapt;
  string2array_mapt string2array_map;
  
  exprt ce_value(
    const typet &type,
    const std::string &index,
    const std::string &v,
    bool in_struct) const;
  
  exprt binary2struct(
    const struct_typet &type, 
    const std::string &binary) const;  

  exprt binary2union(
    const union_typet &type, 
    const std::string &binary) const;  

  // flattens multi-operand expressions into binary
  // expressions
  void convert_nary(const exprt &expr, 
                    const irep_idt op_string,
                    bool bool_as_bv);
};

#endif
