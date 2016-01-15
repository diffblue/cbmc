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
#include <util/byte_operators.h>

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
  typedef enum { GENERIC, BOOLECTOR, CVC3, CVC4, MATHSAT, OPENSMT, YICES, Z3 } solvert;

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
    let_id_count(0),
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

    case CVC4:
      break;

    case MATHSAT:
      break;

    case OPENSMT:
      break;
      
    case YICES:
      break;
    
    case Z3:
      use_array_of_bool=true;
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
  virtual void set_frozen(literalt a) { /* not needed */ }
  virtual void set_to(const exprt &expr, bool value);
  virtual exprt get(const exprt &expr) const;
  virtual std::string decision_procedure_text() const { return "SMT2"; }
  virtual void print_assignment(std::ostream &out) const;
  virtual tvt l_get(literalt l) const;
  virtual void set_assumptions(const bvt &bv) { assumptions=bv; }

  // new stuff
  void convert_expr(const exprt &);
  void convert_type(const typet &);
  void convert_literal(const literalt);

protected:
  std::ostream &out;
  std::string benchmark, notes, logic;
  solvert solver;
  
  bvt assumptions;
  boolbv_widtht boolbv_width;
  
  void write_header();
  void write_footer(std::ostream &);

  // tweaks for arrays  
  bool use_array_theory(const exprt &);
  void flatten_array(const exprt &);
  void unflatten_array(const exprt &);
  
  // specific expressions go here
  void convert_byte_update(const byte_update_exprt &expr);
  void convert_byte_extract(const byte_extract_exprt &expr);
  void convert_typecast(const typecast_exprt &expr);
  void convert_floatbv_typecast(const floatbv_typecast_exprt &expr);
  void convert_struct(const struct_exprt &expr);
  void convert_union(const union_exprt &expr);
  void convert_constant(const constant_exprt &expr);
  void convert_relation(const exprt &expr);
  void convert_is_dynamic_object(const exprt &expr);
  void convert_plus(const plus_exprt &expr);
  void convert_minus(const minus_exprt &expr);
  void convert_div(const div_exprt &expr);
  void convert_mult(const mult_exprt &expr);
  void convert_rounding_mode_FPA(const exprt &expr);
  void convert_floatbv_plus(const ieee_float_op_exprt &expr);
  void convert_floatbv_minus(const ieee_float_op_exprt &expr);
  void convert_floatbv_div(const ieee_float_op_exprt &expr);
  void convert_floatbv_mult(const ieee_float_op_exprt &expr);
  void convert_mod(const mod_exprt &expr);
  void convert_index(const index_exprt &expr);
  void convert_member(const member_exprt &expr);
  void convert_overflow(const exprt &expr);
  void convert_with(const with_exprt &expr);
  void convert_update(const exprt &expr);
  
  std::string convert_identifier(const irep_idt &identifier);
  
  // introduces a let-expression for operands
  exprt convert_operands(const exprt &);
  
  // auxiliary methods
  void find_symbols(const exprt &expr);
  void find_symbols(const typet &type);
  void find_symbols_rec(const typet &type, std::set<irep_idt> &recstack);

  // letification
  typedef std::pair<unsigned, symbol_exprt> let_count_id;
  typedef hash_map_cont<exprt, let_count_id, irep_hash> seen_expressionst;
  unsigned let_id_count;
  const static unsigned LET_COUNT = 2;

  class let_visitort : public expr_visitort
  {
    const seen_expressionst &let_map;

  public:
    let_visitort(const seen_expressionst &map):let_map(map) { }
    
    void operator()(exprt &expr)
    {
      seen_expressionst::const_iterator it = let_map.find(expr);
      if (it != let_map.end() &&
          it->second.first >= LET_COUNT)
      {
        symbol_exprt symb = it->second.second;
        expr = symb;
        return;
      }
    }
  };
  
  exprt letify(exprt &expr);
  exprt letify_rec(
    exprt &expr,
    std::vector<exprt>& let_order,
    const seen_expressionst& map,
    unsigned i);

  void collect_bindings(
    exprt &expr,
    seen_expressionst &map,
    std::vector<exprt> &let_order);

  exprt substitute_let(
    exprt &expr,
    const seen_expressionst &map);

  // Parsing solver responses  
  constant_exprt parse_literal(const irept &, const typet &type);
  exprt parse_struct(const irept &s, const struct_typet &type);
  exprt parse_union(const irept &s, const union_typet &type);
  exprt parse_array(const irept &s, const array_typet &type);
  exprt parse_rec(const irept &s, const typet &type);
  
  // we use this to build a bit-vector encoding of the FPA theory
  void convert_floatbv(const exprt &expr);
  static std::string type2id(const typet &);
  static std::string floatbv_suffix(const exprt &);
  std::set<irep_idt> bvfp_set; // already converted
  
  class smt2_symbolt:public exprt
  {
  public:
    smt2_symbolt(const irep_idt &_identifier, const typet &_type):
      exprt(ID_smt2_symbol, _type)
    { set(ID_identifier, _identifier); }
      
    inline const irep_idt &get_identifier() const
    {
      return get(ID_identifier);
    }
  };

  inline const smt2_symbolt &to_smt2_symbol(const exprt &expr)
  {
    assert(expr.id()==ID_smt2_symbol && !expr.has_operands());
    return static_cast<const smt2_symbolt&>(expr);
  }
  
  // flattens any non-bitvector type into a bitvector,
  // e.g., booleans, vectors, structs, arrays but also
  // floats when using the FPA theory.
  // unflatten() does the opposite.
  typedef enum { BEGIN, END } wheret;
  void flatten2bv(const exprt &);
  void unflatten(wheret, const typet &, unsigned nesting=0);
  
  // pointers
  pointer_logict pointer_logic;
  void convert_address_of_rec(
    const exprt &expr, const pointer_typet &result_type);

  void define_object_size(const irep_idt &id, const exprt &expr);

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

  defined_expressionst object_sizes;

  typedef std::set<std::string> smt2_identifierst;
  smt2_identifierst smt2_identifiers;

  // Boolean part
  unsigned no_boolean_variables;
  std::vector<bool> boolean_assignment;
};

#endif
