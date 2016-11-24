#include <util/options.h>

template<class preproct>
genetic_preprocessingt<preproct>::genetic_preprocessingt(
    const optionst &options, preproct &preproc) :
    options(options), preproc(preproc)
{
}

template<class preproct>
genetic_preprocessingt<preproct>::~genetic_preprocessingt()
{
}

template<class preproct>
size_t genetic_preprocessingt<preproct>::get_min_solution_size() const
{
  return preproc.get_min_solution_size();
}

template<class preproct>
void genetic_preprocessingt<preproct>::operator()()
{
  preproc();
}

template<class preproct>
void genetic_preprocessingt<preproct>::operator()(
    const size_t max_solution_length)
{
  preproc(options.get_unsigned_int_option("cegis-max-size"));
}
