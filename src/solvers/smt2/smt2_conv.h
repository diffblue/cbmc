/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT2_SMT2_CONV_H
#define CPROVER_SOLVERS_SMT2_SMT2_CONV_H

#include <sstream>
#include <set>

#include <util/std_expr.h>
#include <util/byte_operators.h>

#ifndef HASH_CODE
#include <util/irep_hash_container.h>
#endif

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/pointer_logic.h>

#include "letify.h"

class typecast_exprt;
class constant_exprt;
class index_exprt;
class member_exprt;

class smt2_convt : public stack_decision_proceduret
{
public:
  enum class solvert
  {
    GENERIC,
    BOOLECTOR,
    CPROVER_SMT2,
    CVC3,
    CVC4,
    MATHSAT,
    YICES,
    Z3
  };

  smt2_convt(
    const namespacet &_ns,
    const std::string &_benchmark,
    const std::string &_notes,
    const std::string &_logic,
    solvert _solver,
    std::ostream &_out)
    : use_FPA_theory(false),
      use_datatypes(false),
      use_array_of_bool(false),
      emit_set_logic(true),
      ns(_ns),
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
    case solvert::GENERIC:
      break;

    case solvert::BOOLECTOR:
      break;

    case solvert::CPROVER_SMT2:
      use_array_of_bool = true;
      emit_set_logic = false;
      break;

    case solvert::CVC3:
      break;

    case solvert::CVC4:
      break;

    case solvert::MATHSAT:
      break;

    case solvert::YICES:
      break;

    case solvert::Z3:
      use_array_of_bool=true;
      emit_set_logic=false;
      use_datatypes=true;
      break;
    }

    write_header();
  }

  ~smt2_convt() override = default;
  resultt dec_solve() override;

  bool use_FPA_theory;
  bool use_datatypes;
  bool use_array_of_bool;
  bool emit_set_logic;

  exprt handle(const exprt &expr) override;
  void set_to(const exprt &expr, bool value) override;
  exprt get(const exprt &expr) const override;
  std::string decision_procedure_text() const override
  {
    return "SMT2";
  }
  void print_assignment(std::ostream &out) const override;

  /// Unimplemented
  void push() override;

  /// Currently, only implements a single stack element (no nested contexts)
  void push(const std::vector<exprt> &_assumptions) override;

  /// Currently, only implements a single stack element (no nested contexts)
  void pop() override;

  void convert_expr(const exprt &);
  void convert_type(const typet &);
  void convert_literal(const literalt);

  std::size_t get_number_of_solver_calls() const override;

protected:
  const namespacet &ns;
  std::ostream &out;
  std::string benchmark, notes, logic;
  solvert solver;

  std::vector<exprt> assumptions;
  boolbv_widtht boolbv_width;

  std::size_t number_of_solver_calls = 0;

  void write_header();
  void write_footer(std::ostream &);

  // tweaks for arrays
  bool use_array_theory(const exprt &);
  void flatten_array(const exprt &);

  // specific expressions go here
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

  void convert_with(const with_exprt &expr);
  void convert_update(const exprt &expr);

  std::string convert_identifier(const irep_idt &identifier);

  literalt convert(const exprt &expr);
  tvt l_get(literalt l) const;

  // auxiliary methods
  exprt prepare_for_convert_expr(const exprt &expr);
  exprt lower_byte_operators(const exprt &expr);
  void find_symbols(const exprt &expr);
  void find_symbols(const typet &type);
  void find_symbols_rec(const typet &type, std::set<irep_idt> &recstack);

  // letification
  letifyt letify;

  // Parsing solver responses
  constant_exprt parse_literal(const irept &, const typet &type);
  struct_exprt parse_struct(const irept &s, const struct_typet &type);
  exprt parse_union(const irept &s, const union_typet &type);
  exprt parse_array(const irept &s, const array_typet &type);
  exprt parse_rec(const irept &s, const typet &type);

  // we use this to build a bit-vector encoding of the FPA theory
  void convert_floatbv(const exprt &expr);
  std::string type2id(const typet &) const;
  std::string floatbv_suffix(const exprt &) const;
  std::set<irep_idt> bvfp_set; // already converted

  class smt2_symbolt : public nullary_exprt
  {
  public:
    smt2_symbolt(const irep_idt &_identifier, const typet &_type)
      : nullary_exprt(ID_smt2_symbol, _type)
    { set(ID_identifier, _identifier); }

    const irep_idt &get_identifier() const
    {
      return get(ID_identifier);
    }
  };

  const smt2_symbolt &to_smt2_symbol(const exprt &expr)
  {
    assert(expr.id()==ID_smt2_symbol && !expr.has_operands());
    return static_cast<const smt2_symbolt&>(expr);
  }

  // flattens any non-bitvector type into a bitvector,
  // e.g., booleans, vectors, structs, arrays but also
  // floats when using the FPA theory.
  // unflatten() does the opposite.
  enum class wheret { BEGIN, END };
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
    bool is_bound;
    typet type;
    exprt value;

    identifiert() : is_bound(false)
    {
      type.make_nil();
      value.make_nil();
    }
  };

  typedef std::unordered_map<irep_idt, identifiert> identifier_mapt;

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
  std::size_t no_boolean_variables;
  std::vector<bool> boolean_assignment;
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_CONV_H
