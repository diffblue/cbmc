#include <util/options.h>

#include <cegis/options/parameters.h>

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
template<class randomt>
ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::ga_learnt(
    const optionst &options, randomt &random, selectt &select, mutatet &mutate,
    crosst &cross, fitnesst &fitness, convertt &convert) :
    options(options), havoc([&random](individualt &ind)
    { random.havoc(ind);}), select(select), mutate(mutate), cross(cross), fitness(
        fitness), convert(convert), program_startup(clockt::now()), max_runtime_in_seconds(
        options.get_unsigned_int_option(CEGIS_MAX_RUNTIME))
{
}

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
template<class seedt>
void ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::seed(
    seedt &seeder)
{
  fitness.seed(seeder);
  const size_t pop_size=options.get_unsigned_int_option(CEGIS_POPSIZE);
  pop.resize(pop_size);
  for (individualt &ind : pop)
    havoc(ind);
  typename populationt::iterator ind=pop.begin();
  std::advance(ind, rand() % pop.size());
  convert.convert(current_candidate, *ind);
}

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
const typename ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::candidatet &ga_learnt<
    selectt, mutatet, crosst, fitnesst, convertt>::next_candidate() const
{
  return current_candidate;
}

namespace
{
bool roll_rate(const int rate)
{
  return rand() < RAND_MAX / 100 * rate;
}

bool should_mutate(const optionst &opt)
{
  return roll_rate(opt.get_unsigned_int_option("cegis-genetic-mutation-rate"));
}

bool should_replace(const optionst &opt)
{
  return roll_rate(opt.get_unsigned_int_option("cegis-genetic-replace-rate"));
}
}

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
bool ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::set_fitness(
    individualt &ind)
{
  // XXX: Specific optimisation for PLDI 2016 submissions.
  mutate.post_process(ind);
  // XXX: Specific optimisation for PLDI 2016 submissions.
  fitness.set_fitness(ind);
  typedef typename individualt::fitnesst target_fitnesst;
  const target_fitnesst target_fitness=fitness.get_target_fitness();
  const bool have_solution=(target_fitness == ind.fitness);
  if (have_solution) convert.convert(current_candidate, ind);
  return have_solution;
}

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
template<class itert>
bool ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::learn(itert first,
    const itert &last)
{
  for (; first != last; ++first)
    fitness.add_test_case(*first);

  const typename selectt::populationt::iterator it=fitness.init(pop);
  if (pop.end() != it)
  {
    convert.convert(current_candidate, *it);
    return true;
  }

  typename selectt::selectiont selection;
  while (!is_evolving || is_evolving())
  {
    if (std::chrono::duration_cast<std::chrono::milliseconds>(clockt::now() - program_startup)
        > std::chrono::seconds(max_runtime_in_seconds)) return false;
    selection=select.select(pop);
    if (should_mutate(options))
    {
      if (!selection.can_mutate()) return false;
      individualt &lhs=selection.mutation_lhs();
      mutate(lhs, selection.mutation_rhs());
      if (set_fitness(lhs)) return true;
    } else if (should_replace(options))
    {
      individualt &ind=*selection.children.back();
      mutate.havoc(ind);
      if (set_fitness(ind)) return true;
    } else
    {
      if (!selection.can_cross()) return false;
      cross(selection.parents, selection.children);
      for (const typename populationt::iterator &child : selection.children)
        if (set_fitness(*child)) return true;
    }
  }
  return false;
}

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
void ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::show_candidate(
    messaget::mstreamt &os) const
{
  show_candidate(os, current_candidate);
}

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
void ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::show_candidate(
    messaget::mstreamt &os, const candidatet &candidate) const
{
  convert.show(os, candidate);
}

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
void ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::set_termination_condition(
    const std::function<bool(void)> is_evolving)
{
  this->is_evolving=is_evolving;
}

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
void ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::set_solution_size_range(
    const size_t min, const size_t max)
{
  // TODO: ga_learn currently gets this info directly from the options. Refactor!
}

template<class selectt, class mutatet, class crosst, class fitnesst,
    class convertt>
void ga_learnt<selectt, mutatet, crosst, fitnesst, convertt>::add_paragon(
    individualt ind)
{
  const size_t num_sacrifices=std::max(size_t(1u), pop.size() / 200);
  const size_t rounds=10u;
  typename populationt::iterator sacrifice=pop.end();
  for (size_t s=0; s < num_sacrifices; ++s)
  {
    for (size_t round=0; round < rounds; ++round)
    {
      typename populationt::iterator candidate=pop.begin();
      std::advance(candidate, rand() % pop.size());
      if (pop.end() == sacrifice || sacrifice->fitness < candidate->fitness)
        sacrifice=candidate;
    }
    *sacrifice=ind;
    set_fitness(*sacrifice);
    assert(sacrifice->fitness == fitness.get_target_fitness());
  }
}
