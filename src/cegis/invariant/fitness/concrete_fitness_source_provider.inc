#include <cegis/invariant/util/invariant_constraint_variables.h>

template<class progt, class configt>
concrete_fitness_source_providert<progt, configt>::concrete_fitness_source_providert(
    const progt &prog, const std::function<size_t(void)> max_size,
    const std::string &execute_func_name) :
    prog(prog), learn_config(prog), max_size(max_size), execute_func_name(
        execute_func_name)
{
}

template<class progt, class configt>
concrete_fitness_source_providert<progt, configt>::~concrete_fitness_source_providert()
{
}

template<class progt, class configt>
std::string concrete_fitness_source_providert<progt, configt>::operator ()()
{
  if (!source.empty()) return source;
  constraint_varst ce_vars;
  get_invariant_constraint_vars(ce_vars, prog);
  const size_t max_prog_size=max_size();
  learn_config.process(max_prog_size);
  const symbol_tablet &st(learn_config.get_symbol_table());
  const goto_functionst &gf=learn_config.get_goto_functions();
  const size_t num_vars=learn_config.get_num_vars();
  const size_t num_consts=learn_config.get_num_consts();
  return post_process_fitness_source(source, st, gf, ce_vars.size(), num_vars,
      num_consts, max_prog_size, execute_func_name);
}
