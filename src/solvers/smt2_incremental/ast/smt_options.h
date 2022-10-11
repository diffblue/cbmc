// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_OPTIONS_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_OPTIONS_H

#include <util/irep.h>

class smt_option_const_downcast_visitort;

class smt_optiont : protected irept
{
public:
  // smt_optiont does not support the notion of an empty / null state. Use
  // optionalt<smt_optiont> instead if an empty option is required.
  smt_optiont() = delete;

  using irept::pretty;

  bool operator==(const smt_optiont &) const;
  bool operator!=(const smt_optiont &) const;

  void accept(smt_option_const_downcast_visitort &) const;
  void accept(smt_option_const_downcast_visitort &&) const;

  /// \brief Class for adding the ability to up and down cast smt_optiont to and
  ///   from irept. These casts are required by other irept derived classes in
  ///   order to store instances of smt_optiont inside them.
  /// \tparam derivedt The type of class which derives from this class and from
  ///   irept.
  template <typename derivedt>
  class storert
  {
  protected:
    storert();
    static irept upcast(smt_optiont option);
    static const smt_optiont &downcast(const irept &);
  };

protected:
  explicit smt_optiont(irep_idt id);
};

template <typename derivedt>
smt_optiont::storert<derivedt>::storert()
{
  static_assert(
    std::is_base_of<irept, derivedt>::value &&
      std::is_base_of<storert<derivedt>, derivedt>::value,
    "Only irept based classes need to upcast smt_termt to store it.");
}

template <typename derivedt>
irept smt_optiont::storert<derivedt>::upcast(smt_optiont option)
{
  return static_cast<irept &&>(std::move(option));
}

template <typename derivedt>
const smt_optiont &smt_optiont::storert<derivedt>::downcast(const irept &irep)
{
  return static_cast<const smt_optiont &>(irep);
}

class smt_option_produce_modelst : public smt_optiont
{
public:
  explicit smt_option_produce_modelst(bool setting);
  bool setting() const;
};

class smt_option_const_downcast_visitort
{
public:
#define OPTION_ID(the_id)                                                      \
  virtual void visit(const smt_option_##the_id##t &) = 0;
#include "smt_options.def"
#undef OPTION_ID
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_OPTIONS_H
