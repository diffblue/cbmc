#include <algorithm>

#include <cegis/invariant/options/parameters.h>
#include <cegis/invariant/symex/learn/instrument_vars.h>
#include <cegis/danger/options/danger_program.h>

template<class preproct>
danger_program_genetic_settingst<preproct>::danger_program_genetic_settingst(
    const optionst &opt, const danger_programt &prog, preproct &preproc) :
    opt(opt), prog(prog), preproc(preproc)
{
}

template<class preproct>
danger_program_genetic_settingst<preproct>::~danger_program_genetic_settingst()
{
}

template<class preproct>
size_t danger_program_genetic_settingst<preproct>::min_prog_sz(
    const size_t prog_index)
{
  return preproc.get_min_solution_size();
}

namespace
{
const size_t SKOLEM_PROG_INDEX=2u;
const size_t PROGS_PER_LOOP=3u;
}

template<class preproct>
size_t danger_program_genetic_settingst<preproct>::max_prog_sz(
    const size_t prog_index)
{
  const size_t user_max_prog_size=opt.get_unsigned_int_option(CEGIS_MAX_SIZE);
  if (SKOLEM_PROG_INDEX == prog_index % PROGS_PER_LOOP)
  {
    const size_t loop_index=prog_index / PROGS_PER_LOOP;
    const size_t num_skolem=prog.loops[loop_index].skolem_choices.size();
    if (num_skolem == 0u) return 0u;
    return std::max(num_skolem, user_max_prog_size);
  }
  return user_max_prog_size;
}

template<class preproct>
size_t danger_program_genetic_settingst<preproct>::max_prog_sz()
{
  const size_t user_max_prog_size=opt.get_unsigned_int_option(CEGIS_MAX_SIZE);
  const danger_programt::loopst &l=prog.loops;
  const size_t max_num_skolem=
      std::max_element(l.begin(), l.end(),
          [](const danger_programt::loopt &l, const danger_programt::loopt &r)
          { return l.skolem_choices.size() < r.skolem_choices.size();})->skolem_choices.size();
  return std::max(max_num_skolem, user_max_prog_size);
}

namespace
{
const size_t NUM_PROG_TYPES=3u;
}

template<class preproct>
size_t danger_program_genetic_settingst<preproct>::num_progs()
{
  return NUM_PROG_TYPES * prog.loops.size();
}

template<class preproct>
size_t danger_program_genetic_settingst<preproct>::num_vars()
{
  invariant_variable_idst vars;
  get_invariant_variable_ids(prog.st, vars);
  return vars.size();
}

template<class preproct>
size_t danger_program_genetic_settingst<preproct>::num_consts()
{
  invariant_variable_idst vars;
  return get_invariant_variable_ids(prog.st, vars);
}

template<class preproct>
size_t danger_program_genetic_settingst<preproct>::num_x0()
{
  return prog.x0_choices.size();
}
