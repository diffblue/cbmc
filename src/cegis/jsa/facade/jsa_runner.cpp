#include <util/options.h>

#include <cegis/facade/cegis.h>
#include <cegis/options/parameters.h>
#include <cegis/seed/null_seed.h>

#include <cegis/symex/cegis_symex_learn.h>
#include <cegis/symex/cegis_symex_verify.h>
#include <cegis/jsa/preprocessing/jsa_preprocessing.h>
#include <cegis/jsa/learn/jsa_symex_learn.h>
#include <cegis/jsa/verify/jsa_symex_verify.h>
#include <cegis/jsa/facade/jsa_runner.h>

namespace
{
typedef messaget::mstreamt mstreamt;
}

int run_jsa(optionst &o, mstreamt &result, const symbol_tablet &st,
    const goto_functionst &gf)
{
  jsa_preprocessingt prep(o, st, gf);
  const size_t max_sz=o.get_unsigned_int_option(CEGIS_MAX_SIZE);
  const null_seedt seed;
  const jsa_programt &prog=prep.get_jsa_program();
  jsa_symex_learnt lcfg(prog);
  cegis_symex_learnt<jsa_preprocessingt, jsa_symex_learnt> learn(o, prep, lcfg);
  jsa_symex_verifyt vcfg(prog);
  cegis_symex_verifyt<jsa_symex_verifyt> oracle(o, vcfg);
  return run_cegis(learn, oracle, prep, seed, max_sz, result);
}
