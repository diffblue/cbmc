/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_SMT2_CONV_H
#define CPROVER_SOLVER_SMT2_CONV_H

#include <sstream>
#include <set>

#include <util/hash_cont.h>
#include <util/std_expr.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/pointer_logic.h>

class typecast_exprt;
class constant_exprt;
class index_exprt;
class member_exprt;

class smt2_convt:public prop_convt
{
public:
  typedef enum { GENERIC, BOOLECTOR, CVC3, MATHSAT, YICES, Z3 } solvert;

  smt2_convt(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic,
    solvert _solver,
    std::ostream &_out):
    prop_convt(_ns),
    use_FPA_theory(false),
    use_datatypes(false),
    use_array_of_bool(false),
    emit_set_logic(true),
    out(_out),
    benchmark(_benchmark),
    notes(_notes),
    logic(_logic),
    solver(_solver),
    boolbv_width(_ns),
    pointer_logic(_ns),
    no_boolean_variables(0)
  {
    // We set some defaults differently
    // for some solvers.

    switch(solver)
    {
    case GENERIC:
      break;
    
    case BOOLECTOR:
      break;
      
    case CVC3:
      break;

    case MATHSAT:
      use_FPA_theory=true;
      break;
      
    case YICES:
      break;
    
    case Z3:
      use_array_of_bool=true;
      use_FPA_theory=true;
      emit_set_logic=false;
      use_datatypes=true;
      break;
    }

    write_header();
  }

  virtual ~smt2_convt() { }
  virtual resultt dec_solve();

  bool use_FPA_theory;
  bool use_datatypes;
  bool use_array_of_bool;
  bool emit_set_logic;

  // overloading interfaces
  virtual literalt convert(const exprt &expr);
  virtual void set_to(const exprt &expr, bool value);
  virtual exprt get(const exprt &expr) const;
  virtual std::string decision_procedure_text() const { return "SMT2"; }
  virtual void print_assignment(std::ostream &out) const;
  virtual tvt l_get(const literalt l) const;
  virtual void set_assumptions(const bvt &bv) { assumptions=bv; }

protected:
  std::ostream &out;
  std::string benchmark, notes, logic;
  solvert solver;
  
  bvt assumptions;
  boolbv_widtht boolbv_width;
  
  void write_header();
  void write_footer();

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
  
  std::string convert_identifier(const irep_idt &identifier);
  
  // auxiliary methods
  void find_symbols(const exprt &expr);
  void find_symbols(const typet &type);
  void find_symbols_rec(const typet &type, std::set<irep_idt> &recstack);

  constant_exprt parse_literal(const std::string &s, const typet &type);
  exprt parse_struct(const std::string &s, const typet &type);
  
  // flattens any non-bitvector type into a bitvector,
  // e.g., booleans, vectors, structs, arrays, ...
  // unflatten() does the opposite.
  typedef enum { BEGIN, END } wheret;
  void flatten2bv(const exprt &);
  void unflatten(wheret, const typet &);
  
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
  
  // for replacing various defined expressions:
  //
  // ID_array_of
  // ID_array
  // ID_string_constant

  typedef std::map<exprt, irep_idt> defined_expressionst;
  defined_expressionst defined_expressions;

  typedef std::set<std::string> smt2_identifierst;
  smt2_identifierst smt2_identifiers;

  // Boolean part
  unsigned no_boolean_variables;
  std::vector<bool> boolean_assignment;
};

#endif
