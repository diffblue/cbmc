/*******************************************************************\

Module: Replication Reducing Abstraction

Author: Adrian Palacios accorell@amazon.com
        Murali Talupur  talupur@amazon.com
        Lefan Zhang     lefanz@amazon.com

\*******************************************************************/

/// \file
/// Replication Reducing Abstraction (RRA) for getting unbounded proofs.
/// Similar to abstractions used in protocol verification, RRA feature
/// reduces large data structures to small sizes by tracking a few
/// locations precisely and conservatively over-approximating other
/// locations. For instance, an array might be abstracted by tracking just
/// one location precisely. All locations before it are lumped into one
/// abstract location and similarly, all locations after it. This "shape" can
/// be viewed as being similar to the regex "*c*".
/// To use this feature user specifies a json file with arrays/strings
/// to be abstracted along with the locations to keep precise, relation
/// between them, helper functions for abstracting the other locations.
/// See regression/rra folder for some examples.
/// This resulting program over-approximates the actual program and
/// since the array/string has a small size the loop unwinding in CBMC
/// can be small while still giving us an unbounded proof.

#ifndef CPROVER_GOTO_INSTRUMENT_RRA_H
#define CPROVER_GOTO_INSTRUMENT_RRA_H

#include <util/expr.h>
#include <util/json.h>
#include <util/options.h>
#include <util/ui_message.h>

#include <goto-programs/goto_model.h>

#include "rra_spec.h"

// class am_abstractiont
class rrat
{
protected:
  // class to find out type relations between exprs
  // this is used to identify symbols we need to abstract
  // given a target array
  // call solve() after reading in all exprs and adding needed links
  // This expr-type_relation is a class that do graph analysis
  // on expressions in the program
  // Each expr is a node in the graph
  // If two exprs should be abstracted in the same way
  // (e.g. A is typecast of B; there is A=B; etc.),
  // there should be an edge between them.
  // If the same expr appears twice in the program, there will be two nodes.
  // The class analyzes the program and constructs this graph.
  // Then it does closure analysis to
  // figure out which entities need to be abstracted.
  // say if we have
  //     buf.a = buf_t.a
  //     buf_t.a = len
  // nodes: 0(buf.a), 1(buf_t.a), 2(buf_t.a), 3(len)
  // edges: {0: [1], 1: [0], 2: [3], 3: [2]}
  //        ==implicitly added edges between the same symbol==>
  //        {0: [1], 1: [0, 2], 2: [3, 1], 3: [2]}
  // symbols: {"buf.a": [0], "buf_t.a": [1,2], "len": [3]}
  class expr_type_relationt
  {
  protected:
    // equiv edges: two nodes should have the same entity_type
    // (e.g. ARRAY, SCALAR, ...)
    std::vector<std::unordered_set<size_t>> edges_equiv;
    // access edges: a-b means that b is an index access to a (a[b])
    std::vector<std::unordered_set<size_t>> edges_access;
    std::vector<exprt> expr_list; // Ordered list of expressions

    // Store information about which nodes are entities/symbols
    // (var or member of struct)
    std::unordered_map<irep_idt, std::unordered_set<size_t>> symbols;
    std::unordered_map<irep_idt, std::unordered_set<irep_idt>>
      entity_edges_equiv;
    std::unordered_map<irep_idt, std::unordered_set<irep_idt>>
      entity_edges_addr_of;

    std::unordered_map<size_t, rra_spect::spect::entityt::entityt_type> todo;
    // entities that are already added
    std::unordered_map<size_t, rra_spect::spect::entityt::entityt_type>
      finished;

    // the variables specified to be abstracted in the first place
    std::unordered_map<irep_idt, rra_spect::spect::entityt::entityt_type> seeds;
    // the new variables/entities found in the closure analysis to be abstracted
    std::unordered_map<irep_idt, rra_spect::spect::entityt::entityt_type>
      new_entities;

  public:
    explicit expr_type_relationt(const rra_spect::spect &spec);

    // add an equiv edge between node i1 and node i2 in the exprt graph
    // this means node i1 and node i2 should be abstracted with the same
    // shape and type.
    void link_exprt_equiv(size_t i1, size_t i2);
    // add an access edge from node i1 to node i2 in the exprt graph
    // this means node i2 is an access to node i1 (<node i1>[<node i2>])
    void link_exprt_access(size_t i1, size_t i2);

    // add an equiv edge between symb1 and symb2 in the entity graph
    // this means the two entities are equivalent in terms of abstraction
    void link_entity_equiv(irep_idt symb1, irep_idt symb2);
    // add an addr_of edge from symb1 to symb2
    // this means symb1 = &symb2
    void link_entity_addr_of(irep_idt symb1, irep_idt symb2);

    // add an exprt in the exprt graph and return its node id
    size_t add_expr(const exprt &expr);

    // get all neighbors of an exprt given a type
    std::vector<std::pair<size_t, rra_spect::spect::entityt::entityt_type>>
    get_neighbors(size_t index, rra_spect::spect::entityt::entityt_type type);

    // this will get two symbol's relation if we have a path of symb1 to symb2
    // the return value is how many addr_of edges we have in the path
    // note that there might be cycles in the symb relation path,
    // but we only count the shortest path
    // e.g. a - b -addrof-> c
    // get_equiv_symb_level(a, c) = 1
    // get_equiv_symb_level(a, b) = 0
    // if no path, return -1
    int check_symb_deref_level(irep_idt symb1, irep_idt symb2);

    // tell whether two symbs are equivalent.
    // This not only checks direct equiv edges, but also
    // checks whether they are equivalent because of
    // chain relations in the entity graph
    bool is_equiv_entity(irep_idt symb1, irep_idt symb2);

    void solve();

    std::unordered_map<irep_idt, rra_spect::spect::entityt::entityt_type>
    get_new_entities();
  };

  // get the string representation from a "symbol" exprt
  // e.g.
  // symbol: <expr's name>
  // member: <ptr's name>->member or <obj's name>.member
  static irep_idt get_string_id_from_exprt(const exprt &expr);
  // is an expr entity?
  // e.g. a.len, b->len, a, b are entities
  // *(a+1).len are not considered entities by us
  static bool is_entity_expr(const exprt &expr);

  /// get the parent of an id
  /// e.g. symb.a.len => (".", "symb.a"), symb->b => ("->", "symb")
  /// \return a pair (flag, parent_name)
  /// flag is one of "" (not having a parent),
  /// "->"(parent is a pointer) and
  /// "."(parent is a struct)
  static std::pair<std::string, irep_idt> get_parent_id(const irep_idt &id);

  /// check if an expr is array_of or dereference
  /// \return flag: 0(none); 1(array_of) -1(dereference)
  static rra_spect::spect::func_call_arg_namet::arg_translate_typet
  check_expr_is_address_or_deref(const exprt &expr, exprt &next_layer);

  static irep_idt check_expr_is_symbol(const exprt &expr);

  /// update the etr object by analyzing all instructions from a function
  /// we are updating both the exprt graph and entity graph in etr
  static std::unordered_set<irep_idt> update_relation_graph_from_function(
    const goto_functiont &goto_function,
    expr_type_relationt &etr,
    goto_modelt &goto_model);

  /// Same function as the previous one,
  /// but doing closure analysis across functions (globally)
  static std::unordered_set<irep_idt>
  complete_the_global_abst_spec(goto_modelt &goto_model, rra_spect &abst_spec);

  /// \param expr: the expression to be checked
  /// \param abst_spec: the rra_spect for the current function
  ///          which contains all spects
  /// \return whether the expr contains an entity to be abstracted
  static bool contains_an_entity_to_be_abstracted(
    const exprt &expr,
    const rra_spect &abst_spec);

  static irep_idt get_abstract_name(const irep_idt &old_name);

  static irep_idt get_const_c_str_len_name(const irep_idt &c_str_name);

  /// \param expr: the expression to be checked
  /// \return whether the expr contains a function call
  static bool contains_a_function_call(const exprt &expr);

  /// \param expr: the expression to be checked.
  ///          this should be called after abst_read
  /// \param abst_spec: the abstraction spec containing all info
  /// \return a list of exprts that directly access abst arrays
  static std::vector<exprt>
  get_direct_access_exprs(const exprt &expr, const rra_spect::spect &spec);

  /// \param expr: the expr to be modified.
  ///          It should be a boolean expr used in assert inst
  /// \param expr_before_abst: the exprt before we do abstract_read.
  ///          This is used to check function calls and abst indices
  /// \param abst_spec: the abstration information for the current function
  /// \param goto_model: the goto_model
  /// \param current_func: the name of the current function
  /// \param insts_before: instructions that need to be added before the
  ///          instruction to support the write
  /// \param insts_after: instructions that need to be added after the
  ///          instruction to support the write
  /// \param new_symbs: new symbols to be added to support the write
  /// \return an exprt that will be evaluated true if there are abstract
  ///         indices in expr. This is used to modify assertions.
  ///         Assertions should be evaluated true if there are non-concrete
  ///         abst indices in it. This should be called after abst_read on expr
  static exprt add_guard_expression_to_assert(
    const exprt &expr,
    const exprt &expr_before_abst,
    const rra_spect &abst_spec,
    const goto_modelt &goto_model,
    const irep_idt &current_func,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  /// \param goto_model: the goto model
  /// \param func_name: the target function
  /// \param abst_spec: the abstraction specification
  /// The function helps declare the abstract variables in the abst_spec
  /// For each variable "var_name", the function inserts the abstracted version
  /// into the symbol table with name "var_name$abst"
  /// If it is a local variable in the function, we'll also change the
  /// declaration for the abstracted variable to "var_name$abst"
  /// If it is a function argument, we'll change the
  /// parameter table (var_name => var_name$abst)
  static void declare_abst_variables(
    goto_modelt &goto_model,
    const std::unordered_set<irep_idt> &functions,
    const rra_spect &abst_spec);

  /// \param expr: the expression to be checked
  /// \param abst_spec: the abstraction specification
  /// \param index: if this exprt is abstract,
  /// \return whether it is abstract, the spec will be put here
  static bool check_if_exprt_eval_to_abst_index(
    const exprt &expr,
    const rra_spect &abst_spec,
    rra_spect::spect &spec);

  // push concrete index values in to function call's operands
  static void push_concrete_indices_to_operands(
    exprt::operandst &operands,
    const rra_spect::spect &spec,
    const goto_modelt &goto_model);

  /// \param func_name: The name of the function call.
  /// \param operands: The operands for the function call.
  /// \param caller: the name of the caller function.
  ///          This is used to create temp variable
  /// \param insts_before: It will put the instructions that declare
  ///          the temp variable here.
  /// \param insts_after: It will put the instructions that unclare
  ///          the temp variable here.
  /// \param new_symbs: The new introduced symbol will be stored here.
  /// \return the tmp variable's symbolt that contains the return value of the
  ///         function call. This function creates a function call given the
  ///         func_name and operands. The function to be called should already
  ///         exist in the goto_model.
  static symbolt create_function_call(
    const irep_idt &func_name,
    const std::vector<exprt> operands,
    const irep_idt &caller,
    const goto_modelt &goto_model,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  /// \param target_expr: the target expression.
  /// \param caller: the name of the caller function.
  ///          This is used to create temp variable
  /// \param insts_before: It will put the instructions that declare
  ///          the temp variable here.
  /// \param insts_after: It will put the instructions that unclare
  ///          the temp variable here.
  /// \param new_symbs: The new introduced symbol will be stored here.
  /// \return the tmp variable's symbolt that contains the return value of the
  ///         assignment. This function creates an assignment that stores a
  ///         given expression
  static symbolt create_temp_var_for_expr(
    const exprt &target_expr,
    const irep_idt &caller,
    const goto_modelt &goto_model,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  /// \param real_lhs: the final lhs that is assigned
  /// \param spec: the spect used for the abstraction
  /// \param caller: the current function, used to generate temp var's name
  /// \param goto_model: the goto_model
  /// \param insts_before: It will put the instructions that declare
  ///          the temp variable here.
  /// \param insts_after: It will put the instructions that unclare
  ///          the temp variable here.
  /// \param new_symbs: The new introduced symbol will be stored here.
  /// \return the temp variable used to call the abstracion function
  /// This function creates an abst function wrap after the current function.
  /// e.g.
  /// orig:
  ///   a = func(xxx)
  /// new:
  ///   tmp_a = func(xxx)
  ///   a = abst(tmp_a) <==== this function creates this inst and return tmp_a
  static symbolt create_abstract_func_after(
    const exprt &real_lhs,
    const rra_spect::spect &spec,
    const irep_idt &caller,
    const goto_modelt &goto_model,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  /// \param expr: the lhs expression to be written to
  /// \param abst_spec: the abstration information for the current function
  /// \param goto_model: the goto_model
  /// \param current_func: the name of the current function
  /// \param insts_before: instructions that need to be added before the
  ///          instruction to support the write
  /// \param insts_after: instructions that need to be added after the
  ///          instruction to support the write
  /// \param new_symbs: new symbols to be added to support the write
  /// \return an exprt that is abstracted
  static exprt abstract_expr_write(
    const exprt &expr,
    const rra_spect &abst_spec,
    const goto_modelt &goto_model,
    const irep_idt &current_func,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  /// \param orig_expr: the original expr, both ops should already
  ///          been abstracted
  /// \param spec: the spec for both op0 and op1
  /// \param goto_model: the goto model
  /// \param caller: the caller function
  /// \param insts_before: instructions to insert before it
  /// \param insts_after: instructions to insert after it
  /// \param new_symbs: symbols to be inserted
  /// \return an exprt of the comparison
  /// This function creates an exprt that compares two abstract indices
  static exprt create_comparator_expr_abs_abs(
    const exprt &orig_expr,
    const rra_spect::spect &spec,
    const goto_modelt &goto_model,
    const irep_idt &caller,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  // abst_read for comparator
  static exprt abstract_expr_read_comparator(
    const exprt &expr,
    const rra_spect &abst_spec,
    const goto_modelt &goto_model,
    const irep_idt &current_func,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  // check whether an expr is a pointer offset
  static bool is_pointer_offset(const exprt &expr);

  // abst_read for plus/minus
  static exprt abstract_expr_read_plusminus(
    const exprt &expr,
    const rra_spect &abst_spec,
    const goto_modelt &goto_model,
    const irep_idt &current_func,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  // abst_read for dereference
  static exprt abstract_expr_read_dereference(
    const exprt &expr,
    const rra_spect &abst_spec,
    const goto_modelt &goto_model,
    const irep_idt &current_func,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  // abst_read for index
  // a[i]
  // a is dynamic: dereference(a+i)
  // a is static: index(a, i)
  static exprt abstract_expr_read_index(
    const exprt &expr,
    const rra_spect &abst_spec,
    const goto_modelt &goto_model,
    const irep_idt &current_func,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  // abst_read for address_of
  static exprt abstract_expr_read_address_of(
    const exprt &expr,
    const rra_spect &abst_spec,
    const goto_modelt &goto_model,
    const irep_idt &current_func,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  /// \param expr: the expression to be read
  /// \param abst_spec: the abstration information for the current function
  /// \param goto_model: the goto_model
  /// \param current_func: the name of the current function
  /// \param insts_before: instructions that need to be added before
  ///          the instruction to support the read
  /// \param insts_after: instructions that need to be added after the
  ///          instruction to support the read
  /// \param new_symbs: new symbols to be added to support the read
  /// \return an exprt that is abstracted
  static exprt abstract_expr_read(
    const exprt &expr,
    const rra_spect &abst_spec,
    const goto_modelt &goto_model,
    const irep_idt &current_func,
    goto_programt::instructionst &insts_before,
    goto_programt::instructionst &insts_after,
    std::vector<symbolt> &new_symbs);

  // add the assumption len=$clen for all length variables
  static void
  add_length_assumptions(goto_modelt &goto_model, const rra_spect &abst_spec);

  // define concrete indices globally
  static void
  define_concrete_indices(goto_modelt &goto_model, const rra_spect &abst_spec);

  // define the length for const c string variables
  // (the place where '0' appears the first)
  static void define_const_c_str_lengths(
    goto_modelt &goto_model,
    const rra_spect &abst_spec);

  // insert the assumptions about the shape's concrete indices
  static void
  insert_shape_assumptions(goto_modelt &goto_model, const rra_spect &abst_spec);

public:
  // link abst functions to goto programs
  static void link_abst_functions(
    goto_modelt &goto_model,
    const rra_spect &abst_spec,
    ui_message_handlert &msg_handler,
    const optionst &options);

  // abstract goto programs
  static void
  abstract_goto_program(goto_modelt &goto_model, rra_spect &abst_spec);
};

#endif // CPROVER_GOTO_INSTRUMENT_RRA_H
