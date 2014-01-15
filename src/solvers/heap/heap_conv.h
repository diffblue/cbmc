/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_HEAP_CONV_H
#define CPROVER_SOLVER_HEAP_CONV_H

#include <sstream>
#include <set>

#include <util/hash_cont.h>
#include <util/std_expr.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/pointer_logic.h>

#include "heaptransformer.h"

class typecast_exprt;
class constant_exprt;
class index_exprt;
class member_exprt;

class heap_convt:public prop_convt
{
public:
  heap_convt(
    const namespacet &_ns):
    prop_convt(_ns),
    use_FPA_theory(false),
    use_datatypes(false),
    use_array_of_bool(false),
    emit_set_logic(true),
    boolbv_width(_ns),
    pointer_logic(_ns),
    array_index_bits(32),
    no_boolean_variables(0),
    no_tmp_variables(0)
  {
    formula.clear();
    boolean_assignment.clear();
  }

  virtual ~heap_convt() { }
  virtual resultt dec_solve();

  bool use_FPA_theory;
  bool use_datatypes;
  bool use_array_of_bool;
  bool emit_set_logic;

  // overloading interfaces
  virtual literalt convert(const exprt &expr);
  virtual void set_to(const exprt &expr, bool value);
  virtual exprt get(const exprt &expr) const;
  virtual std::string decision_procedure_text() const { return "hippo"; }
  virtual void print_assignment(std::ostream &out) const;
  virtual tvt l_get(const literalt l) const;
  virtual void set_assumptions(const bvt &bv) { assumptions=bv; }

protected:
  
  bvt assumptions;
  boolbv_widtht boolbv_width;

  // new stuff
  void convert_expr(const exprt &expr);
  void convert_type(const typet &type);
  void convert_literal(const literalt);
  
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
  void convert_floatbv_plus(const exprt &expr);
  void convert_floatbv_minus(const exprt &expr);
  void convert_floatbv_div(const exprt &expr);
  void convert_floatbv_mult(const exprt &expr);
  void convert_mod(const mod_exprt &expr);
  void convert_index(const index_exprt &expr);
  void convert_member(const member_exprt &expr);
  void convert_overflow(const exprt &expr);
  void convert_with(const exprt &expr);
  void convert_update(const exprt &expr);
  
  literalt convert_bool(const exprt &expr);
  literalt convert_equality(const equal_exprt &expr);
  literalt convert_function(const heap_function_application_exprt &expr);
  exprt to_nnf(const exprt &expr);
  exprt to_cnf(const exprt &expr);
  and_exprt distribute(const or_exprt &expr);
  heapexpr convert_heapexpr(const exprt &expr);
  std::string convert_identifier(const irep_idt &identifier);
  
  // auxiliary methods
  void find_symbols(const exprt &expr);
  void find_symbols(const typet &type);
  void find_symbols_rec(const typet &type, std::set<irep_idt> &recstack);

  constant_exprt parse_literal(const std::string &s, const typet &type);
  exprt parse_struct(const std::string &s, const typet &type);
  
  // booleans vs. bv[1]
  void bool2bv(const exprt &);
  void bv2bool(const exprt &);
  
  // arrays
  typet array_index_type() const;
  void array_index(const exprt &expr);

  // pointers
  pointer_logict pointer_logic;
  void convert_address_of_rec(
    const exprt &expr, const pointer_typet &result_type);

  // keeps track of all non-Boolean symbols and their value
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

  // for modeling structs as Z3 datatype, enabled when
  // use_datatype is set
  typedef std::map<typet, std::string> datatype_mapt;
  datatype_mapt datatype_map;
  
  unsigned array_index_bits;
  
  // for replacing various defined expressions:
  //
  // ID_array_of
  // ID_array
  // ID_string_constant

  typedef std::map<exprt, irep_idt> defined_expressionst;
  defined_expressionst defined_expressions;

  typedef std::set<std::string> heap_identifierst;
  heap_identifierst heap_identifiers;

  // Boolean part
  unsigned no_boolean_variables;
  std::vector<bool> boolean_assignment;

  //Heap
  unsigned no_tmp_variables;

  typedef std::map<irep_idt, literalt> symbolst;
  symbolst symbols;

  formulat formula;

  typedef std::map<literalt,exprt> literal_mapt;
  literal_mapt literal_map;

  typedef std::map<unsigned,heaplit*> heap_literal_mapt;
  heap_literal_mapt heap_literal_map;

};

#endif
