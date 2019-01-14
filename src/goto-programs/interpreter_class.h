/*******************************************************************\

Module: Interpreter for GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interpreter for GOTO Programs

#ifndef CPROVER_GOTO_PROGRAMS_INTERPRETER_CLASS_H
#define CPROVER_GOTO_PROGRAMS_INTERPRETER_CLASS_H

#include <stack>

#include <util/arith_tools.h>
#include <util/invariant.h>
#include <util/std_types.h>
#include <util/sparse_vector.h>
#include <util/message.h>

#include "goto_functions.h"
#include "goto_trace.h"
#include "json_goto_trace.h"

class interpretert:public messaget
{
public:
  interpretert(
    const symbol_tablet &_symbol_table,
    const goto_functionst &_goto_functions,
    message_handlert &_message_handler):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    ns(_symbol_table),
    goto_functions(_goto_functions),
    stack_pointer(0),
    done(false),
    stop_on_assertion(false)
  {
    show=true;
  }

  void operator()();
  void print_memory(bool input_flags);

  // An assertion that identifier 'id' carries value in some particular context.
  // Used to record parameter (id) assignment (value) lists for function calls.
  struct function_assignmentt
  {
    irep_idt id;
    exprt value;
  };

  // A list of such assignments.
  typedef std::vector<function_assignmentt> function_assignmentst;

  typedef std::vector<mp_integer> mp_vectort;

  // Maps an assignment id to the name of the parameter being assigned
  typedef std::pair<irep_idt, irep_idt> assignment_idt;

  // Identifies an expression before and after some change;
  typedef std::pair<exprt, exprt> diff_pairt;

  // Records a diff between an assignment pre and post conditions
  typedef std::map<assignment_idt, diff_pairt> side_effects_differencet;

  // A entry in the input_valuest map
  typedef std::pair<irep_idt, exprt> input_entryt;

  // List of the input variables with their corresponding initial values
  typedef std::map<irep_idt, exprt> input_valuest;

  // List of dynamically allocated symbols that are not in the symbol table
  typedef std::map<irep_idt, typet> dynamic_typest;

  typedef std::map<irep_idt, function_assignmentst> output_valuest;
  output_valuest output_values;

  // An assignment list annotated with the calling context.
  struct function_assignments_contextt
  {
    irep_idt calling_function;
    function_assignmentst return_assignments;
    function_assignmentst param_assignments;
    function_assignmentst exception_assignments;
  };

  // list_input_varst maps function identifiers onto a vector of [name = value]
  // assignments per call to that function.
  typedef std::list<function_assignments_contextt>
          function_assignments_contextst;
  typedef std::map<irep_idt, std::list<function_assignments_contextt> >
          list_input_varst;

  const dynamic_typest &get_dynamic_types() { return dynamic_types; }

protected:
  const symbol_tablet &symbol_table;

  // This is a cache so that we don't have to create it when a call needs it
  const namespacet ns;

  const goto_functionst &goto_functions;

  typedef std::unordered_map<irep_idt, mp_integer> memory_mapt;
  typedef std::map<mp_integer, irep_idt> inverse_memory_mapt;
  memory_mapt memory_map;
  inverse_memory_mapt inverse_memory_map;

  const inverse_memory_mapt::value_type &address_to_object_record(
    const mp_integer &address) const
  {
    auto lower_bound=inverse_memory_map.lower_bound(address);
    if(lower_bound->first!=address)
    {
      CHECK_RETURN(lower_bound!=inverse_memory_map.begin());
      --lower_bound;
    }
    return *lower_bound;
  }

  irep_idt address_to_identifier(const mp_integer &address) const
  {
    return address_to_object_record(address).second;
  }

  mp_integer address_to_offset(const mp_integer &address) const
  {
    return address-(address_to_object_record(address).first);
  }

  mp_integer base_address_to_alloc_size(const mp_integer &address) const
  {
    PRECONDITION(address_to_offset(address)==0);
    auto upper_bound=inverse_memory_map.upper_bound(address);
    mp_integer next_alloc_address=
      upper_bound==inverse_memory_map.end() ?
      memory.size() :
      upper_bound->first;
    return next_alloc_address-address;
  }

  mp_integer base_address_to_actual_size(const mp_integer &address) const
  {
    auto memory_iter = memory.find(numeric_cast_v<std::size_t>(address));
    if(memory_iter==memory.end())
      return 0;
    mp_integer ret=0;
    mp_integer alloc_size=base_address_to_alloc_size(address);
    while(memory_iter!=memory.end() && memory_iter->first<(address+alloc_size))
    {
      ++ret;
      ++memory_iter;
    }
    return ret;
  }

  class memory_cellt
  {
  public:
    memory_cellt() :
    value(0),
    initialized(initializedt::UNKNOWN)
    {}
    mp_integer value;
    // Initialized is annotated even during reads
    enum class initializedt
    {
      UNKNOWN,
      WRITTEN_BEFORE_READ,
      READ_BEFORE_WRITTEN
    };
    // Set to 1 when written-before-read, -1 when read-before-written
    mutable initializedt initialized;
  };

  typedef sparse_vectort<memory_cellt> memoryt;
  typedef std::map<std::string, const irep_idt &> parameter_sett;
  // mapping <structure, field> -> value
  typedef std::pair<const irep_idt, const irep_idt> struct_member_idt;
  typedef std::map<struct_member_idt, const exprt> struct_valuest;

  //  The memory is being annotated/reshaped even during reads
  //  (ie to find a read-before-write location) thus memory
  //  properties need to be mutable to avoid making all calls nonconst
  mutable memoryt memory;

  mp_integer stack_pointer;

  void build_memory_map();
  void build_memory_map(const symbolt &symbol);
  mp_integer build_memory_map(const irep_idt &id, const typet &type);
  typet concretize_type(const typet &type);
  bool unbounded_size(const typet &);
  mp_integer get_size(const typet &type);

  struct_typet::componentt get_component(
    const irep_idt &object,
    const mp_integer &offset);

  typet get_type(const irep_idt &id) const;

  exprt get_value(
    const typet &type,
    const mp_integer &offset=0,
    bool use_non_det=false);

  exprt get_value(
    const typet &type,
    mp_vectort &rhs,
    const mp_integer &offset=0);

  exprt get_value(const irep_idt &id);

  void step();

  void execute_assert();
  void execute_assume();
  void execute_assign();
  void execute_goto();
  void execute_function_call();
  void execute_other();
  void execute_decl();
  void clear_input_flags();

  void allocate(
    const mp_integer &address,
    const mp_integer &size);

  void assign(
    const mp_integer &address,
    const mp_vectort &rhs);

  void read(
    const mp_integer &address,
    mp_vectort &dest) const;

  void read_unbounded(
    const mp_integer &address,
    mp_vectort &dest) const;

  virtual void command();

  class stack_framet
  {
  public:
    goto_programt::const_targett return_pc;
    goto_functionst::function_mapt::const_iterator return_function;
    mp_integer return_value_address;
    memory_mapt local_map;
    mp_integer old_stack_pointer;
  };

  typedef std::stack<stack_framet> call_stackt;

  call_stackt call_stack;
  input_valuest input_vars;
  list_input_varst function_input_vars;

  goto_functionst::function_mapt::const_iterator function;
  goto_programt::const_targett pc, next_pc, target_assert;
  goto_tracet steps;
  bool done;
  bool show;
  bool stop_on_assertion;
  static const size_t npos;
  size_t num_steps;
  size_t total_steps;

  dynamic_typest dynamic_types;
  int num_dynamic_objects;
  mp_integer stack_depth;
  unsigned thread_id;

  bool evaluate_boolean(const exprt &expr)
  {
    mp_vectort v;
    evaluate(expr, v);
    if(v.size()!=1)
      throw "invalid boolean value";
    return v.front()!=0;
  }

  bool count_type_leaves(
    const typet &source_type,
    mp_integer &result);

  bool byte_offset_to_memory_offset(
    const typet &source_type,
    const mp_integer &byte_offset,
    mp_integer &result);

  bool memory_offset_to_byte_offset(
    const typet &source_type,
    const mp_integer &cell_offset,
    mp_integer &result);

  void evaluate(
    const exprt &expr,
    mp_vectort &dest);

  mp_integer evaluate_address(const exprt &expr, bool fail_quietly=false);

  void initialize(bool init);
  void show_state();

  friend class interpreter_testt;
};

#endif // CPROVER_GOTO_PROGRAMS_INTERPRETER_CLASS_H
