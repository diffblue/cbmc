#include <cegis/bmc_verification_oracle.h>

bmc_verification_oraclet::bmc_verification_oraclet(const bmct &bmc,
    const goto_functionst &goto_functions) :
    bmc(bmc), goto_functions(goto_functions)
{
}

void bmc_verification_oraclet::verify(const candidatet &candidate)
{
}

bmc_verification_oraclet::counterexamplet bmc_verification_oraclet::get_counterexample() const
{
  return current_counterexample;
}

bool bmc_verification_oraclet::has_counterexample() const
{
  return false;
}

bool bmc_verification_oraclet::success() const
{
  return false;
}
