#include <linking/zero_initializer.h>

#include <cegis/symex/cegis_symex_learn.h>
#include <cegis/symex/cegis_symex_verify.h>
#include <cegis/facade/runner_helper.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/control/value/control_types.h>
#include <cegis/control/preprocessing/control_preprocessing.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/learn/control_symex_learn.h>
#include <cegis/control/learn/rational_solution_configuration.h>
#include <cegis/control/verify/control_symex_verify.h>
#include <cegis/control/facade/control_runner.h>

int run_control(optionst &o, messaget::mstreamt &result,
    const symbol_tablet &st, const goto_functionst &gf)
{
  control_preprocessingt prep(st, gf);
  const control_programt &program=prep.get_program();
  typedef control_symex_learnt<rational_solution_configurationt> control_learnt;
  control_learnt lcfg(program);
  const std::function<void(control_solutiont &)> default_solution=
      [&st](control_solutiont &solution)
      { if (!solution.a.operands().empty()) return;
        const symbol_typet &type=control_solution_type(st);
        const source_locationt loc(default_cegis_source_location());
        const namespacet ns(st);
        null_message_handlert msg;
        const exprt zero(zero_initializer(type, loc, ns, msg));
        const struct_exprt zero_struct=to_struct_expr(zero);
        solution.a=get_a_controller_comp(ns, zero_struct);
        solution.b=get_b_controller_comp(ns, zero_struct);
      };
  cegis_symex_learnt<control_preprocessingt, control_learnt> learn(o,
      prep, lcfg, default_solution);
  control_symex_verifyt vcfg(program);
  cegis_symex_verifyt<control_symex_verifyt> oracle(o, vcfg);
  return run_cegis_with_statistics_wrapper(result, o, learn, oracle, prep);
}
