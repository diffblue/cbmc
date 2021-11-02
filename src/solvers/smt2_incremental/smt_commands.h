// Author: Diffblue Ltd.

#ifndef CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_COMMANDS_H
#define CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_COMMANDS_H

#include <solvers/smt2_incremental/smt_logics.h>
#include <solvers/smt2_incremental/smt_options.h>
#include <solvers/smt2_incremental/smt_terms.h>
#include <util/irep.h>

class smt_command_const_downcast_visitort;

class smt_commandt : protected irept
{
public:
  // smt_commandt does not support the notion of an empty / null state. Use
  // optionalt<smt_commandt> instead if an empty command is required.
  smt_commandt() = delete;

  using irept::pretty;

  bool operator==(const smt_commandt &) const;
  bool operator!=(const smt_commandt &) const;

  void accept(smt_command_const_downcast_visitort &) const;
  void accept(smt_command_const_downcast_visitort &&) const;

protected:
  using irept::irept;
};

class smt_assert_commandt : public smt_commandt,
                            private smt_termt::storert<smt_assert_commandt>
{
public:
  explicit smt_assert_commandt(smt_termt condition);
  const smt_termt &condition() const;
};

class smt_check_sat_commandt : public smt_commandt
{
public:
  smt_check_sat_commandt();
};

class smt_declare_function_commandt
  : public smt_commandt,
    private smt_sortt::storert<smt_declare_function_commandt>,
    private smt_termt::storert<smt_declare_function_commandt>
{
public:
  smt_declare_function_commandt(
    smt_identifier_termt identifier,
    std::vector<smt_sortt> parameter_sorts);
  const smt_identifier_termt &identifier() const;
  const smt_sortt &return_sort() const;
  std::vector<std::reference_wrapper<const smt_sortt>> parameter_sorts() const;

private:
  using sort_storert = smt_sortt::storert<smt_declare_function_commandt>;
  using term_storert = smt_termt::storert<smt_declare_function_commandt>;
};

class smt_define_function_commandt
  : public smt_commandt,
    private smt_termt::storert<smt_define_function_commandt>
{
public:
  smt_define_function_commandt(
    irep_idt identifier,
    std::vector<smt_identifier_termt> parameters,
    smt_termt definition);
  const smt_identifier_termt &identifier() const;
  std::vector<std::reference_wrapper<const smt_identifier_termt>>
  parameters() const;
  const smt_sortt &return_sort() const;
  const smt_termt &definition() const;
};

class smt_exit_commandt : public smt_commandt
{
public:
  smt_exit_commandt();
};

class smt_get_value_commandt : public smt_commandt,
                               protected smt_termt::storert<smt_assert_commandt>
{
public:
  /// \brief This constructor constructs the `get-value` command, such that it
  ///   stores a single descriptor for which the solver will be commanded to
  ///   respond with a value.
  /// \note This class currently supports storing a single descriptor only,
  ///   whereas the SMT-LIB standard version 2.6 supports one or more
  ///   descriptors. Getting one value at a time is currently sufficient for our
  ///   requirements. This class could be expanded should there be a need to get
  ///   multiple values at once.
  explicit smt_get_value_commandt(smt_termt descriptor);
  const smt_termt &descriptor() const;
};

class smt_push_commandt : public smt_commandt
{
public:
  explicit smt_push_commandt(std::size_t levels);
  size_t levels() const;
};

class smt_pop_commandt : public smt_commandt
{
public:
  explicit smt_pop_commandt(std::size_t levels);
  size_t levels() const;
};

class smt_set_logic_commandt
  : public smt_commandt,
    private smt_logict::storert<smt_set_logic_commandt>
{
public:
  explicit smt_set_logic_commandt(smt_logict logic);
  const smt_logict &logic() const;
};

class smt_set_option_commandt
  : public smt_commandt,
    private smt_optiont::storert<smt_set_option_commandt>
{
public:
  explicit smt_set_option_commandt(smt_optiont option);
  const smt_optiont &option() const;
};

class smt_command_const_downcast_visitort
{
public:
#define COMMAND_ID(the_id)                                                     \
  virtual void visit(const smt_##the_id##_commandt &) = 0;
#include "smt_commands.def"
#undef COMMAND_ID
};

/// \brief A function generated from a command. Used for validating function
///   application term arguments.
class smt_command_functiont
{
private:
  std::vector<smt_sortt> parameter_sorts;
  smt_identifier_termt _identifier;

public:
  explicit smt_command_functiont(
    const smt_declare_function_commandt &function_declaration);
  explicit smt_command_functiont(
    const smt_define_function_commandt &function_definition);
  irep_idt identifier() const;
  smt_sortt return_sort(const std::vector<smt_termt> &arguments) const;
  void validate(const std::vector<smt_termt> &arguments) const;
};

#endif // CPROVER_SOLVERS_SMT2_INCREMENTAL_SMT_COMMANDS_H
