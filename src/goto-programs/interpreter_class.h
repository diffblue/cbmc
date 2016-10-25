#include <stack>

#include <util/arith_tools.h>

#include "goto_functions.h"
#include "goto_trace.h"
#include "json_goto_trace.h"
#include "util/message.h"
#include "util/options.h"

/*******************************************************************\

   Class: interpretert

 Purpose: interpreter for GOTO programs

\*******************************************************************/

class interpretert
{
public:
  // An assertion that identifier 'id' carries value 'value' in some particular context.
  struct function_assignmentt {
    irep_idt id;
    exprt value;
  };

  // A list of such assignments.
  typedef std::vector<function_assignmentt> function_assignmentst;
  typedef std::map<std::pair<const irep_idt, const irep_idt>,
                   std::pair<const exprt, const exprt>> side_effects_differencet;

  interpretert(
    const symbol_tablet &_symbol_table,
    const goto_functionst &_goto_functions,
    messaget *_message_handler,
    const optionst& options):
  symbol_table(_symbol_table),
  ns(_symbol_table),
    goto_functions(_goto_functions)
  {
    message = _message_handler;
  }
  
  void operator()();
  
  friend class simplify_evaluatet;

  typedef std::map<const irep_idt,exprt> input_varst;
  typedef std::map<const irep_idt,irep_idt> input_var_functionst;
  typedef std::map<const irep_idt,const typet> dynamic_typest;

  // An assignment list annotated with the calling context.
  struct function_assignments_contextt {
    irep_idt calling_function;
    function_assignmentst return_assignments;
    function_assignmentst param_assignments;
  };
  
  // list_input_varst maps function identifiers onto a vector of [name = value] assignments
  // per call to that function.
  typedef std::list<function_assignments_contextt> function_assignments_contextst;
  typedef std::map<const irep_idt,std::list<function_assignments_contextt> > list_input_varst;
  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> memory_mapt;

protected:
  const symbol_tablet &symbol_table;
  const namespacet ns;
  const goto_functionst &goto_functions;
  messaget *message;
  mutable dynamic_typest dynamic_types;
  mutable memory_mapt memory_map;
  
  class memory_cellt
  {
  public:
    irep_idt identifier;
    unsigned offset;
    mp_integer value;
    mutable char initialised;
  };
  
  typedef std::vector<memory_cellt> memoryt;
  mutable memoryt memory;
  
  unsigned stack_pointer;
  
  void build_memory_map();
  void build_memory_map(const symbolt &symbol);
  mp_integer build_memory_map(const irep_idt &id,const typet &type) const;
  typet concretise_type(const typet &type) const;
  unsigned get_size(const typet &type) const;

  irep_idt get_component_id(const irep_idt &object,unsigned offset);
public:
  typet get_type(const irep_idt &id) const;
  exprt get_value(const typet &type,unsigned offset=0,bool use_non_det = false);
  exprt get_value(const typet &type,std::vector<mp_integer> &rhs,unsigned offset=0);
  exprt get_value(const irep_idt &id);
  void get_value_tree(const irep_idt& capture_symbol, function_assignmentst& captured);
  void get_value_tree_bu(const irep_idt& capture_symbol, function_assignmentst& captured);
  void get_value_tree(const exprt& capture_expr, function_assignmentst& captured);
  mp_integer get_this_address(const code_function_callt&);
  char is_opaque_function(const goto_programt::instructionst::const_iterator &it,irep_idt &function_id);


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
    mp_integer address,
    unsigned size);

  void assign(
    mp_integer address,
    const std::vector<mp_integer> &rhs);

  void read(
    mp_integer address,
    std::vector<mp_integer> &dest) const;

  void command();

  class stack_framet
  {
  public:
    goto_programt::const_targett return_PC;
    goto_functionst::function_mapt::const_iterator return_function;
    mp_integer return_value_address;
    memory_mapt local_map;
    unsigned old_stack_pointer;
  };

  typedef std::stack<stack_framet> call_stackt;
  
  call_stackt call_stack;  
  input_varst input_vars;
  input_var_functionst input_first_assignments;
  list_input_varst function_input_vars;
  
  goto_functionst::function_mapt::const_iterator function;
  goto_programt::const_targett PC, next_PC,targetAssert;
  goto_tracet steps;
  bool done;
  bool show;
  bool stop_on_assertion;
  size_t num_steps;
  size_t total_steps;
  mutable int num_dynamic_objects;
  size_t stack_depth;
  int thread_id;

  bool evaluate_boolean(const exprt &expr) const
  {
    std::vector<mp_integer> v;
    evaluate(expr, v);
    if(v.size()!=1) throw "invalid boolean value";
    return v.front()!=0;
  }

  bool extract_member_at(
    std::vector<mp_integer>::iterator& source_iter,
    const std::vector<mp_integer>::iterator source_end,
    const typet& source_type,
    mp_integer offset,
    const typet& target_type,
    std::vector<mp_integer> &dest,
    bool should_return_this) const;

  bool get_cell_byte_offset(
    const typet& source_type,
    mp_integer& cell_offset,
    mp_integer& result) const;
  
  void evaluate(
    const exprt &expr,
    std::vector<mp_integer> &dest) const;
  
  mp_integer evaluate_address(const exprt &expr, bool fail_quietly=false) const;
  
  void initialise(bool init);
  void show_state();

  void list_inputs(bool use_non_det = false);
  void list_inputs(input_varst &inputs);
  void fill_inputs(input_varst &inputs);
  void list_non_bodied();
  void list_non_bodied(const goto_programt::instructionst &instructions);
  void print_inputs();
  void print_memory(bool input_flags);

  goto_programt::const_targett getPC(const unsigned location,bool &ok);
  void prune_inputs(input_varst &inputs,list_input_varst& function_inputs, const bool filter);

 public:
  input_varst& load_counter_example_inputs(const std::string &filename);
  input_varst& load_counter_example_inputs(const goto_tracet &trace, list_input_varst& opaque_function_returns, side_effects_differencet &, const bool filtered=false);
  const input_var_functionst& get_input_first_assignments() { return input_first_assignments; }
  const dynamic_typest& get_dynamic_types() { return dynamic_types; }
};
