/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_SMT2_SMT2_CONV_H
#define CPROVER_SOLVERS_SMT2_SMT2_CONV_H

#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/threeval.h>

#include <map>
#include <set>
#include <sstream>

#if !HASH_CODE
#  include <util/irep_hash_container.h>
#endif

#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/pointer_logic.h>
#include <solvers/prop/literal.h>
#include <solvers/stack_decision_procedure.h>

#include "letify.h"

class floatbv_typecast_exprt;
class ieee_float_op_exprt;
class union_typet;

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
    std::ostream &_out);

  ~smt2_convt() override = default;

  bool use_FPA_theory;
  bool use_array_of_bool;
  bool use_as_const;
  bool use_check_sat_assuming;
  bool use_datatypes;
  bool use_lambda_for_array;
  bool emit_set_logic;

  exprt handle(const exprt &expr) override;
  void set_to(const exprt &expr, bool value) override;
  exprt get(const exprt &expr) const override;
  std::string decision_procedure_text() const override;
  void print_assignment(std::ostream &out) const override;

  /// Unimplemented
  void push() override;

  /// Currently, only implements a single stack element (no nested contexts)
  void push(const std::vector<exprt> &_assumptions) override;

  /// Currently, only implements a single stack element (no nested contexts)
  void pop() override;

  std::size_t get_number_of_solver_calls() const override;

  static std::string convert_identifier(const irep_idt &identifier);

protected:
  const namespacet &ns;
  std::ostream &out;
  std::string benchmark, notes, logic;
  solvert solver;

  std::vector<exprt> assumptions;
  boolbv_widtht boolbv_width;

  std::size_t number_of_solver_calls = 0;

  resultt dec_solve() override;

  void write_header();
  /// Writes the end of the SMT file to the `smt_convt::out` stream. These parts
  /// of the output may be changed when using multiple rounds of solving. They
  /// include the following parts of the output file -
  ///  * The object size definitions.
  ///  * The assertions based on the `assumptions` member variable.
  ///  * The `(check-sat)` or `check-sat-assuming` command.
  ///  * A `(get-value |identifier|)` command for each of the identifiers in
  ///    `smt2_convt::smt2_identifiers`.
  ///  * An `(exit)` command.
  void write_footer();

  // tweaks for arrays
  bool use_array_theory(const exprt &);
  void flatten_array(const exprt &);

  // specific expressions go here
  void convert_typecast(const typecast_exprt &expr);
  void convert_floatbv_typecast(const floatbv_typecast_exprt &expr);
  void convert_struct(const struct_exprt &expr);
  void convert_union(const union_exprt &expr);
  void convert_constant(const constant_exprt &expr);
  void convert_relation(const binary_relation_exprt &);
  void convert_is_dynamic_object(const unary_exprt &);
  void convert_plus(const plus_exprt &expr);
  void convert_minus(const minus_exprt &expr);
  void convert_div(const div_exprt &expr);
  void convert_mult(const mult_exprt &expr);
  void convert_rounding_mode_FPA(const exprt &expr);
  void convert_floatbv_plus(const ieee_float_op_exprt &expr);
  void convert_floatbv_minus(const ieee_float_op_exprt &expr);
  void convert_floatbv_div(const ieee_float_op_exprt &expr);
  void convert_floatbv_mult(const ieee_float_op_exprt &expr);
  void convert_floatbv_rem(const binary_exprt &expr);
  void convert_mod(const mod_exprt &expr);
  void convert_euclidean_mod(const euclidean_mod_exprt &expr);
  void convert_index(const index_exprt &expr);
  void convert_member(const member_exprt &expr);

  void convert_with(const with_exprt &expr);
  void convert_update(const exprt &expr);

  void convert_expr(const exprt &);
  void convert_type(const typet &);
  void convert_literal(const literalt);

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
  /// This function is for parsing array output from SMT solvers
  /// when "(get-value |???|)" returns an array object.
  /// \param s: is the irept parsed from the SMT output
  /// \param type: is the expected type
  /// \returns an exprt that represents the array
  exprt parse_array(const irept &s, const array_typet &type);
  exprt parse_rec(const irept &s, const typet &type);
  /// This function walks the SMT output and populates a
  /// map with index/value pairs for the array
  /// \param operands_map: is a map of the operands to the array
  ///    being constructed indexed by their index.
  /// \param src: is the irept source for the SMT output
  /// \param type: is the type of the array
  void walk_array_tree(
    std::unordered_map<int64_t, exprt> *operands_map,
    const irept &src,
    const array_typet &type);

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

  void define_object_size(const irep_idt &id, const object_size_exprt &expr);

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

  // for modeling structs as SMT datatype when use_datatype is set
  //
  // it maintains a map of `struct_typet` or `struct_tag_typet`
  // to datatype names declared in SMT
  typedef std::map<typet, std::string> datatype_mapt;
  datatype_mapt datatype_map;

  // for replacing various defined expressions:
  //
  // ID_array_of
  // ID_array
  // ID_string_constant

  typedef std::map<exprt, irep_idt> defined_expressionst;
  defined_expressionst defined_expressions;
  /// The values which boolean identifiers have been `smt2_convt::set_to` or
  /// in other words those which are asserted as true / false in the output
  /// smt2 formula.
  std::unordered_map<irep_idt, bool> set_values;

  std::map<object_size_exprt, irep_idt> object_sizes;

  typedef std::set<std::string> smt2_identifierst;
  smt2_identifierst smt2_identifiers;

  // Boolean part
  std::size_t no_boolean_variables;
  std::vector<bool> boolean_assignment;
};

#endif // CPROVER_SOLVERS_SMT2_SMT2_CONV_H
