#include <cegis/symex/cegis_symex_learn.h>
#include <cegis/symex/cegis_symex_verify.h>
#include <cegis/facade/runner_helper.h>
#include <cegis/control/preprocessing/control_preprocessing.h>
#include <cegis/control/learn/control_symex_learn.h>
#include <cegis/control/verify/control_symex_verify.h>
#include <cegis/control/facade/control_runner.h>

int run_control(optionst &o, messaget::mstreamt &result,
    const symbol_tablet &st, const goto_functionst &gf)
{
  control_preprocessingt prep(st, gf);
  const control_programt &program=prep.get_program();
  const control_symex_learnt lcfg(program);
  cegis_symex_learnt<control_preprocessingt,
                     const control_symex_learnt> learn(o, prep, lcfg);
  control_symex_verifyt vcfg(program);
  cegis_symex_verifyt<control_symex_verifyt> oracle(o, vcfg);
  return run_cegis_with_statistics_wrapper(result, o, learn, oracle, prep);
}
