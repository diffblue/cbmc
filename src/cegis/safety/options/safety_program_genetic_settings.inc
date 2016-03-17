#include <algorithm>

#include <cegis/invariant/options/parameters.h>
#include <cegis/invariant/symex/learn/instrument_vars.h>
#include <cegis/safety/options/safety_program.h>

template<class preproct>
safety_program_genetic_settingst<preproct>::safety_program_genetic_settingst(
    const optionst &opt, const safety_programt &prog, preproct &preproc) :
    opt(opt), prog(prog), preproc(preproc)
{
}

template<class preproct>
safety_program_genetic_settingst<preproct>::~safety_program_genetic_settingst()
{
}

namespace
{
const size_t MIN_PROG_SZ=1u;
}

template<class preproct>
size_t safety_program_genetic_settingst<preproct>::min_prog_sz(
    const size_t prog_index)
{
  return std::max(MIN_PROG_SZ, preproc.get_min_solution_size());
}

template<class preproct>
size_t safety_program_genetic_settingst<preproct>::max_prog_sz(
    const size_t prog_index)
{
  return max_prog_sz();
}

template<class preproct>
size_t safety_program_genetic_settingst<preproct>::max_prog_sz()
{
  const size_t user_max_prog_size=opt.get_unsigned_int_option(CEGIS_MAX_SIZE);
  return std::max(min_prog_sz(0u), user_max_prog_size);
}

template<class preproct>
size_t safety_program_genetic_settingst<preproct>::num_progs()
{
  return prog.safety_loops.size();
}

template<class preproct>
size_t safety_program_genetic_settingst<preproct>::num_vars()
{
  invariant_variable_idst vars;
  get_invariant_variable_ids(prog.st, vars);
  return vars.size();
}

template<class preproct>
size_t safety_program_genetic_settingst<preproct>::num_consts()
{
  invariant_variable_idst vars;
  return get_invariant_variable_ids(prog.st, vars);
}

template<class preproct>
size_t safety_program_genetic_settingst<preproct>::num_x0()
{
  return 0u;
}
