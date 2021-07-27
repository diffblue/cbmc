// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_logics.h>

// Define the irep_idts for logics.
#define LOGIC_ID(the_id, the_name)                                             \
  const irep_idt ID_smt_logic_##the_id{"smt_logic_" #the_id};
#include <solvers/smt2_incremental/smt_logics.def>
#undef LOGIC_ID

bool smt_logict::operator==(const smt_logict &other) const
{
  return irept::operator==(other);
}

bool smt_logict::operator!=(const smt_logict &other) const
{
  return !(*this == other);
}

template <typename visitort>
void accept(const smt_logict &logic, const irep_idt &id, visitort &&visitor)
{
#define LOGIC_ID(the_id, the_name)                                             \
  if(id == ID_smt_logic_##the_id)                                              \
    return visitor.visit(static_cast<const smt_logic_##the_id##t &>(logic));
// The include below is marked as nolint because including the same file
// multiple times is required as part of the x macro pattern.
#include <solvers/smt2_incremental/smt_logics.def> // NOLINT(build/include)
#undef LOGIC_ID
  UNREACHABLE;
}

void smt_logict::accept(smt_logic_const_downcast_visitort &visitor) const
{
  ::accept(*this, id(), visitor);
}

void smt_logict::accept(smt_logic_const_downcast_visitort &&visitor) const
{
  ::accept(*this, id(), std::move(visitor));
}

#define LOGIC_ID(the_id, the_name)                                             \
  smt_logic_##the_id##t::smt_logic_##the_id##t()                               \
    : smt_logict{ID_smt_logic_##the_id}                                        \
  {                                                                            \
  }
#include "smt_logics.def"
#undef LOGIC_ID
