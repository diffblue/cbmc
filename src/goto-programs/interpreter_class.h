#include <stack>

#include <util/arith_tools.h>

#include "goto_functions.h"
#include "goto_trace.h"
#include "json_goto_trace.h"

/*******************************************************************\

   Class: interpretert

 Purpose: interpreter for GOTO programs

\*******************************************************************/

class interpretert
{
public:
  interpretert(
    const symbol_tablet &_symbol_table,
    const goto_functionst &_goto_functions):
    symbol_table(_symbol_table),
    ns(_symbol_table),
    goto_functions(_goto_functions)
  {
  }
  
  void operator()();
  
  friend class simplify_evaluatet;

protected:
  const symbol_tablet &symbol_table;
  const namespacet ns;
  const goto_functionst &goto_functions;

  typedef hash_map_cont<irep_idt, unsigned, irep_id_hash> memory_mapt;
  memory_mapt memory_map;
  
  class memory_cellt
  {
  public:
    irep_idt identifier;
    unsigned offset;
    mp_integer value;
    mutable char initialised;
  };
  
  typedef std::vector<memory_cellt> memoryt;
  memoryt memory;
  
  unsigned stack_pointer;
  
  void build_memory_map();
  void build_memory_map(const symbolt &symbol);
  unsigned get_size(const typet &type) const;

  irep_idt get_component_id(irep_idt &object,unsigned offset);
  exprt get_value(const typet &type,unsigned offset=0);
  exprt get_value(const typet &type,std::vector<mp_integer> &rhs,unsigned offset=0);

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
  typedef std::map<irep_idt,exprt> input_varst;
  
  call_stackt call_stack;  
  input_varst input_vars;
  goto_functionst::function_mapt::const_iterator function;
  goto_programt::const_targett PC, next_PC;
  goto_tracet steps;
  bool done;
  bool show;
  int num_steps;
  int stack_depth;
  int thread_id;
  
  bool evaluate_boolean(const exprt &expr) const
  {
    std::vector<mp_integer> v;
    evaluate(expr, v);
    if(v.size()!=1) throw "invalid boolean value";
    return v.front()!=0;
  }

  void evaluate(
    const exprt &expr,
    std::vector<mp_integer> &dest) const;
  
  mp_integer evaluate_address(const exprt &expr) const;
  
  void initialise(bool init);
  void show_state();

  void list_inputs(bool use_non_det = false);
  void list_inputs(input_varst &inputs);
  void print_inputs();
  void fill_inputs(input_varst &inputs);
  input_varst& load_counter_example_inputs(const std::string &filename);
  input_varst& load_counter_example_inputs(goto_tracet &trace);

};
