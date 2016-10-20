#include <util/options.h>

#include <cegis/options/parameters.h>

template<class learnt>
learn_preprocess_seedt<learnt>::learn_preprocess_seedt(const optionst &options,
    learnt &learn) :
    options(options), learn(learn)
{
}

template<class learnt>
template<class cest>
void learn_preprocess_seedt<learnt>::operator()(cest &ces) const
{
  const size_t max_sz=options.get_unsigned_int_option(CEGIS_MAX_SIZE);
  learn.process(max_sz);
}
