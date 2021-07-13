// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_options.h>

// Define the irep_idts for options.
#define OPTION_ID(the_id)                                                      \
  const irep_idt ID_smt_option_##the_id{"smt_option_" #the_id};
#include <solvers/smt2_incremental/smt_options.def>
#undef OPTION_ID

smt_optiont::smt_optiont(const irep_idt id) : irept(id)
{
}

bool smt_optiont::operator==(const smt_optiont &other) const
{
  return irept::operator==(other);
}

bool smt_optiont::operator!=(const smt_optiont &other) const
{
  return !(*this == other);
}

smt_option_produce_modelst::smt_option_produce_modelst(bool setting)
  : smt_optiont{ID_smt_option_produce_models}
{
  set(ID_value, setting);
}

bool smt_option_produce_modelst::setting() const
{
  return get_bool(ID_value);
}

template <typename visitort>
void accept(const smt_optiont &option, const irep_idt &id, visitort &&visitor)
{
#define OPTION_ID(the_id)                                                      \
  if(id == ID_smt_option_##the_id)                                             \
    return visitor.visit(static_cast<const smt_option_##the_id##t &>(option));
// The include below is marked as nolint because including the same file
// multiple times is required as part of the x macro pattern.
#include <solvers/smt2_incremental/smt_options.def> // NOLINT(build/include)
#undef OPTION_ID
  UNREACHABLE;
}

void smt_optiont::accept(smt_option_const_downcast_visitort &visitor) const
{
  ::accept(*this, id(), visitor);
}

void smt_optiont::accept(smt_option_const_downcast_visitort &&visitor) const
{
  ::accept(*this, id(), std::move(visitor));
}
