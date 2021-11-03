// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSES_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSES_H

#include "smt_terms.h"
#include <util/irep.h>

class smt_responset : protected irept
{
public:
  // smt_responset does not support the notion of an empty / null state. Use
  // optionalt<smt_responset> instead if an empty response is required.
  smt_responset() = delete;

  using irept::pretty;

  bool operator==(const smt_responset &) const;
  bool operator!=(const smt_responset &) const;

  template <typename sub_classt>
  const sub_classt *cast() const &;

protected:
  using irept::irept;
};

class smt_success_responset : public smt_responset
{
public:
  smt_success_responset();
};

class smt_check_sat_response_kindt : protected irept
{
public:
  // smt_responset does not support the notion of an empty / null state. Use
  // optionalt<smt_responset> instead if an empty response is required.
  smt_check_sat_response_kindt() = delete;

  using irept::pretty;

  bool operator==(const smt_check_sat_response_kindt &) const;
  bool operator!=(const smt_check_sat_response_kindt &) const;

  template <typename sub_classt>
  const sub_classt *cast() const &;

  /// \brief Class for adding the ability to up and down cast
  ///   smt_check_sat_response_kindt to and from irept. These casts are required
  ///   by other irept derived classes in order to store instances of smt_termt
  ///   inside them.
  /// \tparam derivedt The type of class which derives from this class and from
  ///   irept.
  template <typename derivedt>
  class storert
  {
  protected:
    storert();
    static irept upcast(smt_check_sat_response_kindt check_sat_response_kind);
    static const smt_check_sat_response_kindt &downcast(const irept &);
  };

protected:
  using irept::irept;
};

class smt_sat_responset : public smt_check_sat_response_kindt
{
public:
  smt_sat_responset();
};

class smt_unsat_responset : public smt_check_sat_response_kindt
{
public:
  smt_unsat_responset();
};

class smt_unknown_responset : public smt_check_sat_response_kindt
{
public:
  smt_unknown_responset();
};

class smt_check_sat_responset
  : public smt_responset,
    private smt_check_sat_response_kindt::storert<smt_check_sat_responset>
{
public:
  explicit smt_check_sat_responset(smt_check_sat_response_kindt kind);
  const smt_check_sat_response_kindt &kind() const;
};

class smt_get_value_responset
  : public smt_responset,
    private smt_termt::storert<smt_get_value_responset>
{
public:
  class valuation_pairt : private irept,
                          private smt_termt::storert<valuation_pairt>
  {
  public:
    valuation_pairt() = delete;
    valuation_pairt(smt_termt descriptor, smt_termt value);

    using irept::pretty;

    bool operator==(const valuation_pairt &) const;
    bool operator!=(const valuation_pairt &) const;

    const smt_termt &descriptor() const;
    const smt_termt &value() const;

    friend smt_get_value_responset;
  };

  explicit smt_get_value_responset(std::vector<valuation_pairt> pairs);
  std::vector<std::reference_wrapper<const valuation_pairt>> pairs() const;
};

class smt_unsupported_responset : public smt_responset
{
public:
  smt_unsupported_responset();
};

class smt_error_responset : public smt_responset
{
public:
  explicit smt_error_responset(irep_idt message);
  const irep_idt &message() const;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_RESPONSES_H
