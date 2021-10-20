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
#include <util/std_code.h>
#include <util/std_expr.h>

#include <analyses/cfg_dominators.h>

#include <vector>
#include <list>

class class_hierarchyt;
class prefix_filtert;
class symbol_tablet;
class symbolt;

class java_bytecode_convert_methodt
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
    bool threading_support,
    bool assert_no_exceptions_thrown)
    : log(_message_handler),
      symbol_table(symbol_table),
      ns(symbol_table),
      max_array_length(_max_array_length),
      throw_assertion_error(throw_assertion_error),
      assert_no_exceptions_thrown(assert_no_exceptions_thrown),
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

  void operator()(
    const symbolt &class_symbol,
    const methodt &method,
    const optionalt<prefix_filtert> &method_context)
  {
    convert(class_symbol, method, method_context);
  }

  typedef uint16_t method_offsett;

protected:
  messaget log;
  symbol_table_baset &symbol_table;
  namespacet ns;
  const size_t max_array_length;
  const bool throw_assertion_error;
  const bool assert_no_exceptions_thrown;
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
  method_offsett slots_for_parameters;

public:
  struct holet
  {
    method_offsett start_pc;
    method_offsett length;
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
    bool is_parameter = false;
    std::vector<holet> holes;

    variablet(
      const symbol_exprt &_symbol_expr,
      std::size_t _start_pc,
      std::size_t _length)
      : symbol_expr(_symbol_expr), start_pc(_start_pc), length(_length)
    {
    }

    variablet(
      const symbol_exprt &_symbol_expr,
      std::size_t _start_pc,
      std::size_t _length,
      bool _is_parameter)
      : symbol_expr(_symbol_expr),
        start_pc(_start_pc),
        length(_length),
        is_parameter(_is_parameter)
    {
    }

    variablet(
      const symbol_exprt &_symbol_expr,
      std::size_t _start_pc,
      std::size_t _length,
      bool _is_parameter,
      std::vector<holet> &&_holes)
      : symbol_expr(_symbol_expr),
        start_pc(_start_pc),
        length(_length),
        is_parameter(_is_parameter),
        holes(std::move(_holes))
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

  exprt variable(const exprt &arg, char type_char, size_t address);

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
    std::list<method_offsett> successors;
    std::set<method_offsett> predecessors;
    codet code;
    stackt stack;
    bool done;
  };

public:
  typedef std::map<method_offsett, converted_instructiont> address_mapt;
  typedef std::pair<const methodt &, const address_mapt &> method_with_amapt;
  typedef cfg_dominators_templatet<method_with_amapt, method_offsett, false>
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
    std::vector<method_offsett> branch_addresses;
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
    method_offsett address_start,
    method_offsett address_limit,
    method_offsett next_block_start_address);

  code_blockt &get_or_create_block_for_pcrange(
    block_tree_nodet &tree,
    code_blockt &this_block,
    method_offsett address_start,
    method_offsett address_limit,
    method_offsett next_block_start_address,
    const address_mapt &amap,
    bool allow_merge = true);

  // conversion
  void convert(
    const symbolt &class_symbol,
    const methodt &,
    const optionalt<prefix_filtert> &method_context);

  code_blockt convert_parameter_annotations(
    const methodt &method,
    const java_method_typet &method_type);

  code_blockt convert_instructions(const methodt &);

  codet get_clinit_call(const irep_idt &classname);

  bool is_method_inherited(
    const irep_idt &classname,
    const irep_idt &mangled_method_name) const;

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
    code_blockt &,
    const bytecode_write_typet,
    const irep_idt &);

  void create_stack_tmp_var(
    const std::string &,
    const typet &,
    code_blockt &,
    exprt &);

  std::vector<method_offsett> try_catch_handler(
    method_offsett address,
    const java_bytecode_parse_treet::methodt::exception_tablet &exception_table)
    const;

  void draw_edges_from_ret_to_jsr(
    address_mapt &address_map,
    const std::vector<method_offsett> &jsr_ret_targets,
    const std::vector<
      std::vector<java_bytecode_parse_treet::instructiont>::const_iterator>
      &ret_instructions) const;

  optionalt<exprt> convert_invoke_dynamic(
    const source_locationt &location,
    std::size_t instruction_address,
    const exprt &arg0,
    codet &result_code);

  code_blockt convert_astore(
    const irep_idt &statement,
    const exprt::operandst &op,
    const source_locationt &location);

  code_blockt convert_store(
    const irep_idt &statement,
    const exprt &arg0,
    const exprt::operandst &op,
    const method_offsett address,
    const source_locationt &location);

  static exprt
  convert_aload(const irep_idt &statement, const exprt::operandst &op);

  /// Load reference from local variable.
  /// \p index must be an unsigned byte and an index in the local variable array
  /// of the current frame. The type of the local variable at index \p index
  /// must:
  ///   - be a reference type if \p type_char is 'a'
  ///   - be either boolean, byte, short, int, or char if \p type_char is 'i', a
  ///     typecast to `int` is added if needed
  ///   - match \c java_type_of_char(type_char) otherwise
  /// \return the local variable at \p index
  exprt convert_load(const exprt &index, char type_char, size_t address);

  code_blockt convert_ret(
    const std::vector<method_offsett> &jsr_ret_targets,
    const exprt &arg0,
    const source_locationt &location,
    const method_offsett address);

  code_ifthenelset convert_if_cmp(
    const java_bytecode_convert_methodt::address_mapt &address_map,
    const u1 bytecode,
    const exprt::operandst &op,
    const mp_integer &number,
    const source_locationt &location) const;

  code_ifthenelset convert_if(
    const java_bytecode_convert_methodt::address_mapt &address_map,
    const exprt::operandst &op,
    const irep_idt &id,
    const mp_integer &number,
    const source_locationt &location) const;

  code_ifthenelset convert_ifnonull(
    const java_bytecode_convert_methodt::address_mapt &address_map,
    const exprt::operandst &op,
    const mp_integer &number,
    const source_locationt &location) const;

  code_ifthenelset convert_ifnull(
    const java_bytecode_convert_methodt::address_mapt &address_map,
    const exprt::operandst &op,
    const mp_integer &number,
    const source_locationt &location) const;

  code_blockt convert_iinc(
    const exprt &arg0,
    const exprt &arg1,
    const source_locationt &location,
    method_offsett address);

  exprt::operandst &convert_shl(
    const irep_idt &statement,
    const exprt::operandst &op,
    exprt::operandst &results) const;

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
    const source_locationt &source_location,
    const exprt &arg0,
    const symbol_exprt &symbol_expr,
    bool is_assertions_disabled_field,
    codet &c,
    exprt::operandst &results);

  code_blockt
  convert_putfield(const fieldref_exprt &arg0, const exprt::operandst &op);

  code_blockt convert_putstatic(
    const source_locationt &location,
    const exprt &arg0,
    const exprt::operandst &op,
    const symbol_exprt &symbol_expr);

  void convert_new(
    const source_locationt &location,
    const exprt &arg0,
    codet &c,
    exprt::operandst &results);

  code_blockt convert_newarray(
    const source_locationt &location,
    const irep_idt &statement,
    const exprt &arg0,
    const exprt::operandst &op,
    exprt::operandst &results);

  code_blockt convert_multianewarray(
    const source_locationt &location,
    const exprt &arg0,
    const exprt::operandst &op,
    exprt::operandst &results);

  codet &do_exception_handling(
    const methodt &method,
    const std::set<method_offsett> &working_set,
    method_offsett cur_pc,
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
    class_method_descriptor_exprt &class_method_descriptor,
    codet &c,
    exprt::operandst &results);

  exprt::operandst &convert_const(
    const irep_idt &statement,
    const constant_exprt &arg0,
    exprt::operandst &results) const;

  void convert_dup2_x2(exprt::operandst &op, exprt::operandst &results);

  void convert_dup2_x1(exprt::operandst &op, exprt::operandst &results);

  void convert_dup2(exprt::operandst &op, exprt::operandst &results);

  code_switcht convert_switch(
    const exprt::operandst &op,
    const java_bytecode_parse_treet::instructiont::argst &args,
    const source_locationt &location);

  codet convert_pop(const irep_idt &statement, const exprt::operandst &op);

  friend class java_bytecode_convert_method_unit_testt;
};
#endif
