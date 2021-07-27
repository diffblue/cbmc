// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_LOGICS_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_LOGICS_H

class smt_logic_const_downcast_visitort;

#include <util/irep.h>

class smt_logict : protected irept
{
public:
  // smt_logict does not support the notion of an empty / null state. Use
  // optionalt<smt_logict> instead if an empty logic is required.
  smt_logict() = delete;

  using irept::pretty;

  bool operator==(const smt_logict &) const;
  bool operator!=(const smt_logict &) const;

  void accept(smt_logic_const_downcast_visitort &) const;
  void accept(smt_logic_const_downcast_visitort &&) const;

  /// \brief Class for adding the ability to up and down cast smt_logict to and
  ///   from irept. These casts are required by other irept derived classes in
  ///   order to store instances of smt_logict inside them.
  /// \tparam derivedt The type of class which derives from this class and from
  ///   irept.
  template <typename derivedt>
  class storert
  {
  protected:
    storert();
    static irept upcast(smt_logict logic);
    static const smt_logict &downcast(const irept &);
  };

protected:
  using irept::irept;
};

template <typename derivedt>
smt_logict::storert<derivedt>::storert()
{
  static_assert(
    std::is_base_of<irept, derivedt>::value &&
      std::is_base_of<storert<derivedt>, derivedt>::value,
    "Only irept based classes need to upcast smt_termt to store it.");
}

template <typename derivedt>
irept smt_logict::storert<derivedt>::upcast(smt_logict logic)
{
  return static_cast<irept &&>(std::move(logic));
}

template <typename derivedt>
const smt_logict &smt_logict::storert<derivedt>::downcast(const irept &irep)
{
  return static_cast<const smt_logict &>(irep);
}

#define LOGIC_ID(the_id, the_name)                                             \
  /* NOLINTNEXTLINE(readability/identifiers) cpplint does not match the ## */  \
  class smt_logic_##the_id##t : public smt_logict                              \
  {                                                                            \
  public:                                                                      \
    smt_logic_##the_id##t();                                                   \
  };
#include "smt_logics.def"
#undef LOGIC_ID

class smt_logic_const_downcast_visitort
{
public:
#define LOGIC_ID(the_id, the_name)                                             \
  virtual void visit(const smt_logic_##the_id##t &) = 0;
#include "smt_logics.def"
#undef LOGIC_ID
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_LOGICS_H
