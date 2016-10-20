#include <cegis/options/parameters.h>
#include <cegis/seed/null_seed.h>
#include <cegis/statistics/cegis_statistics_wrapper.h>
#include <cegis/facade/cegis.h>

template<class learnt, class verifyt, class preproct>
int run_cegis_with_statistics_wrapper(messaget::mstreamt &os,
    const optionst &opt, learnt &l, verifyt &v, preproct &p)
{
  null_seedt seed;
  return run_cegis_with_statistics_wrapper(os, opt, l, v, p, seed);
}

template<class learnt, class verifyt, class preproct, class seedt>
int run_cegis_with_statistics_wrapper(messaget::mstreamt &os,
    const optionst &opt, learnt &l, verifyt &v, preproct &p, seedt &seed)
{
  const size_t max_prog_size=opt.get_unsigned_int_option(CEGIS_MAX_SIZE);
  if (!opt.get_bool_option(CEGIS_STATISTICS))
    return run_cegis(l, v, p, seed, max_prog_size, os);
  typedef messaget::mstreamt streamt;
  cegis_statistics_wrappert<learnt, verifyt, streamt> stat(l, v, os, opt);
  return run_cegis(stat, stat, p, seed, max_prog_size, os);
}
