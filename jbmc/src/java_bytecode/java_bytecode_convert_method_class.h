/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAVA Bytecode Language Conversion

#ifndef CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_CLASS_H
#define CPROVER_JAVA_BYTECODE_JAVA_BYTECODE_CONVERT_METHOD_CLASS_H

#include "ci_lazy_methods_needed.h"
#include "java_bytecode_parse_tree.h"
#include "java_bytecode_convert_class.h"

#include <util/expanding_vector.h>
#include <util/message.h>
#include <util/std_types.h>
#include <util/std_expr.h>

#include <analyses/cfg_dominators.h>

#include <vector>
#include <list>

class symbol_tablet;
class symbolt;

class java_bytecode_convert_methodt:public messaget
{
public:
  java_bytecode_convert_methodt(
    symbol_table_baset &symbol_table,
    message_handlert &_message_handler,
    size_t _max_array_length,
    bool throw_assertion_error,
    optionalt<ci_lazy_methods_neededt> needed_lazy_methods,
    java_string_library_preprocesst &_string_preprocess,
    const class_hierarchyt &class_hierarchy,
    bool threading_support)
    : messaget(_message_handler),
      symbol_table(symbol_table),
      max_array_length(_max_array_length),
      throw_assertion_error(throw_assertion_error),
      threading_support(threading_support),
      needed_lazy_methods(std::move(needed_lazy_methods)),
      string_preprocess(_string_preprocess),
      slots_for_parameters(0),
      method_has_this(false),
      class_hierarchy(class_hierarchy)
  {
  }

  typedef java_bytecode_parse_treet::methodt methodt;
  typedef java_bytecode_parse_treet::instructiont instructiont;
  typedef methodt::instructionst instructionst;
  typedef methodt::local_variable_tablet local_variable_tablet;
  typedef methodt::local_variablet local_variablet;

  void operator()(const symbolt &class_symbol, const methodt &method)
  {
    convert(class_symbol, method);
  }

protected:
  symbol_table_baset &symbol_table;
  const size_t max_array_length;
  const bool throw_assertion_error;
  const bool threading_support;
  optionalt<ci_lazy_methods_neededt> needed_lazy_methods;

  /// Fully qualified name of the method under translation.
  /// Initialized by `convert`.
  /// Example: "my.package.ClassName.myMethodName:(II)I"
  irep_idt method_id;

  /// A copy of `method_id` :/
  irep_idt current_method;

  /// Return type of the method under conversion.
  /// Initialized by `convert`.
  typet method_return_type;

  java_string_library_preprocesst &string_preprocess;

  /// Number of local variable slots used by the JVM to pass parameters upon
  /// invocation of the method under translation.
  /// Initialized in `convert`.
  unsigned slots_for_parameters;

public:
  struct holet
  {
    unsigned start_pc;
    unsigned length;
  };

  struct local_variable_with_holest
  {
    local_variablet var;
    bool is_parameter;
    std::vector<holet> holes;
  };

  typedef std::vector<local_variable_with_holest>
    local_variable_table_with_holest;

  class variablet
  {
  public:
    symbol_exprt symbol_expr;
    size_t start_pc;
    size_t length;
    bool is_parameter;
    std::vector<holet> holes;

    variablet() : symbol_expr(), start_pc(0), length(0), is_parameter(false)
    {
    }
  };

protected:
  typedef std::vector<variablet> variablest;
  expanding_vectort<variablest> variables;
  std::set<symbol_exprt> used_local_names;
  bool method_has_this;
  std::map<irep_idt, bool> class_has_clinit_method;
  std::map<irep_idt, bool> any_superclass_has_clinit_method;
  const class_hierarchyt &class_hierarchy;

  enum instruction_sizet
  {
    INST_INDEX = 2,
    INST_INDEX_CONST = 3
  };

  // return corresponding reference of variable
  const variablet &find_variable_for_slot(
    size_t address,
    variablest &var_list);

  // JVM local variables
  enum variable_cast_argumentt
  {
    CAST_AS_NEEDED,
    NO_CAST
  };

  const exprt variable(
    const exprt &arg,
    char type_char,
    size_t address,
    variable_cast_argumentt do_cast);

  // temporary variables
  std::list<symbol_exprt> tmp_vars;

  symbol_exprt tmp_variable(const std::string &prefix, const typet &type);

  // JVM program locations
  static irep_idt label(const irep_idt &address);

  // JVM Stack
  typedef std::vector<exprt> stackt;
  stackt stack;

  exprt::operandst pop(std::size_t n);

  void pop_residue(std::size_t n);

  void push(const exprt::operandst &o);

  /// Returns true iff the slot index of the local variable of a method (coming
  /// from the LVT) is a parameter of that method. Assumes that
  /// `slots_for_parameters` is initialized upon call.
  bool is_parameter(const local_variablet &v)
  {
    return v.index < slots_for_parameters;
  }

  struct converted_instructiont
  {
    converted_instructiont(
      const instructionst::const_iterator &it,
      const codet &_code)
      : source(it), code(_code), done(false)
    {
    }

    instructionst::const_iterator source;
    std::list<unsigned> successors;
    std::set<unsigned> predecessors;
    codet code;
    stackt stack;
    bool done;
  };

public:
  typedef std::map<unsigned, converted_instructiont> address_mapt;
  typedef std::pair<const methodt &, const address_mapt &> method_with_amapt;
  typedef cfg_dominators_templatet<method_with_amapt, unsigned, false>
    java_cfg_dominatorst;

protected:
  void find_initializers(
    local_variable_table_with_holest &vars,
    const address_mapt &amap,
    const java_cfg_dominatorst &doms);

  void find_initializers_for_slot(
    local_variable_table_with_holest::iterator firstvar,
    local_variable_table_with_holest::iterator varlimit,
    const address_mapt &amap,
    const java_cfg_dominatorst &doms);

  void setup_local_variables(const methodt &m, const address_mapt &amap);

  struct block_tree_nodet
  {
    bool leaf;
    std::vector<unsigned> branch_addresses;
    std::vector<block_tree_nodet> branch;

    block_tree_nodet() : leaf(false)
    {
    }

    explicit block_tree_nodet(bool l) : leaf(l)
    {
    }

    static block_tree_nodet get_leaf()
    {
      return block_tree_nodet(true);
    }
  };

  static void replace_goto_target(
    codet &repl,
    const irep_idt &old_label,
    const irep_idt &new_label);

  code_blockt &get_block_for_pcrange(
    block_tree_nodet &tree,
    code_blockt &this_block,
    unsigned address_start,
    unsigned address_limit,
    unsigned next_block_start_address);

  code_blockt &get_or_create_block_for_pcrange(
    block_tree_nodet &tree,
    code_blockt &this_block,
    unsigned address_start,
    unsigned address_limit,
    unsigned next_block_start_address,
    const address_mapt &amap,
    bool allow_merge = true);

  optionalt<symbolt> get_lambda_method_symbol(
    const java_class_typet::java_lambda_method_handlest &lambda_method_handles,
    const size_t index);

  // conversion
  void convert(const symbolt &class_symbol, const methodt &);

  codet convert_instructions(
    const methodt &,
    const java_class_typet::java_lambda_method_handlest &);

  const bytecode_infot &get_bytecode_info(const irep_idt &statement);

  codet get_clinit_call(const irep_idt &classname);

  bool is_method_inherited(
    const irep_idt &classname,
    const irep_idt &methodid) const;

  irep_idt get_static_field(
    const irep_idt &class_identifier, const irep_idt &component_name) const;

  enum class bytecode_write_typet
  {
    VARIABLE,
    ARRAY_REF,
    STATIC_FIELD,
    FIELD
  };

  void save_stack_entries(
    const std::string &,
    const typet &,
    code_blockt &,
    const bytecode_write_typet,
    const irep_idt &);

  void create_stack_tmp_var(
    const std::string &,
    const typet &,
    code_blockt &,
    exprt &);

  std::vector<unsigned int> try_catch_handler(
    unsigned int address,
    const java_bytecode_parse_treet::methodt::exception_tablet &exception_table)
    const;

  void draw_edges_from_ret_to_jsr(
    address_mapt &address_map,
    const std::vector<unsigned int> &jsr_ret_targets,
    const std::vector<
      std::vector<java_bytecode_parse_treet::instructiont>::const_iterator>
      &ret_instructions) const;

  optionalt<exprt> convert_invoke_dynamic(
    const java_class_typet::java_lambda_method_handlest &lambda_method_handles,
    const source_locationt &location,
    const exprt &arg0);

  codet convert_astore(
    const irep_idt &statement,
    const exprt::operandst &op,
    const source_locationt &location);

  codet convert_store(
    const irep_idt &statement,
    const exprt &arg0,
    const exprt::operandst &op,
    const unsigned address,
    const source_locationt &location);

  exprt
  convert_aload(const irep_idt &statement, const exprt::operandst &op) const;

  code_blockt convert_ret(
    const std::vector<unsigned int> &jsr_ret_targets,
    const exprt &arg0,
    const source_locationt &location,
    const unsigned address);

  codet convert_if_cmp(
    const java_bytecode_convert_methodt::address_mapt &address_map,
    const irep_idt &statement,
    const exprt::operandst &op,
    const mp_integer &number,
    const source_locationt &location) const;

  codet convert_if(
    const java_bytecode_convert_methodt::address_mapt &address_map,
    const exprt::operandst &op,
    const irep_idt &id,
    const mp_integer &number,
    const source_locationt &location) const;

  codet convert_ifnonull(
    const java_bytecode_convert_methodt::address_mapt &address_map,
    const exprt::operandst &op,
    const mp_integer &number,
    const source_locationt &location) const;

  codet convert_ifnull(
    const java_bytecode_convert_methodt::address_mapt &address_map,
    const exprt::operandst &op,
    const mp_integer &number,
    const source_locationt &location) const;

  codet convert_iinc(
    const exprt &arg0,
    const exprt &arg1,
    const source_locationt &location,
    unsigned address);

  exprt::operandst &convert_ushr(
    const irep_idt &statement,
    const exprt::operandst &op,
    exprt::operandst &results) const;

  exprt::operandst &
  convert_cmp(const exprt::operandst &op, exprt::operandst &results) const;

  exprt::operandst &convert_cmp2(
    const irep_idt &statement,
    const exprt::operandst &op,
    exprt::operandst &results) const;

  void convert_getstatic(
    const exprt &arg0,
    const symbol_exprt &symbol_expr,
    bool is_assertions_disabled_field,
    codet &c,
    exprt::operandst &results);

  codet convert_putfield(const exprt &arg0, const exprt::operandst &op);

  codet convert_putstatic(
    const source_locationt &location,
    const exprt &arg0,
    const exprt::operandst &op,
    const symbol_exprt &symbol_expr);

  void convert_new(
    const source_locationt &location,
    const exprt &arg0,
    codet &c,
    exprt::operandst &results);

  void convert_newarray(
    const source_locationt &location,
    const irep_idt &statement,
    const exprt &arg0,
    const exprt::operandst &op,
    codet &c,
    exprt::operandst &results);

  void convert_multianewarray(
    const source_locationt &location,
    const exprt &arg0,
    const exprt::operandst &op,
    codet &c,
    exprt::operandst &results);

  codet &do_exception_handling(
    const methodt &method,
    const std::set<unsigned int> &working_set,
    unsigned int cur_pc,
    codet &c);

  void convert_athrow(
    const source_locationt &location,
    const exprt::operandst &op,
    codet &c,
    exprt::operandst &results) const;

  void convert_checkcast(
    const exprt &arg0,
    const exprt::operandst &op,
    codet &c,
    exprt::operandst &results) const;

  codet convert_monitorenterexit(
    const irep_idt &statement,
    const exprt::operandst &op,
    const source_locationt &source_location);

  codet &replace_call_to_cprover_assume(source_locationt location, codet &c);

  void convert_invoke(
    source_locationt location,
    const irep_idt &statement,
    exprt &arg0,
    codet &c,
    exprt::operandst &results);

  exprt::operandst &convert_const(
    const irep_idt &statement,
    const exprt &arg0,
    exprt::operandst &results) const;

  void convert_dup2_x2(exprt::operandst &op, exprt::operandst &results);

  void convert_dup2_x1(exprt::operandst &op, exprt::operandst &results);

  void convert_dup2(exprt::operandst &op, exprt::operandst &results);

  codet convert_switch(
    java_bytecode_convert_methodt::address_mapt &address_map,
    const exprt::operandst &op,
    const java_bytecode_parse_treet::instructiont::argst &args,
    const source_locationt &location);

  codet convert_pop(const irep_idt &statement, const exprt::operandst &op);
};
#endif
