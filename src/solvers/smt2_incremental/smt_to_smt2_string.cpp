// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_to_smt2_string.h>

#include <solvers/smt2/smt2_conv.h>
#include <solvers/smt2_incremental/smt_commands.h>
#include <solvers/smt2_incremental/smt_logics.h>
#include <solvers/smt2_incremental/smt_sorts.h>
#include <solvers/smt2_incremental/smt_terms.h>

#include <util/range.h>
#include <util/string_utils.h>

#include <functional>
#include <iostream>
#include <sstream>
#include <stack>
#include <string>

class smt_sort_output_visitort : public smt_sort_const_downcast_visitort
{
protected:
  std::ostream &os;

public:
  explicit smt_sort_output_visitort(std::ostream &os) : os(os)
  {
  }

  void visit(const smt_bool_sortt &) override
  {
    os << "Bool";
  }

  void visit(const smt_bit_vector_sortt &bit_vec) override
  {
    os << "(_ BitVec " << bit_vec.bit_width() << ")";
  }
};

std::ostream &operator<<(std::ostream &os, const smt_sortt &sort)
{
  sort.accept(smt_sort_output_visitort{os});
  return os;
}

std::string smt_to_smt2_string(const smt_sortt &sort)
{
  std::stringstream ss;
  ss << sort;
  return ss.str();
}

/// \note The printing algorithm in the `smt_term_to_string_convertert` class is
///   implemented using an explicit `std::stack` rather than using recursion
///   and the call stack. This is done in order to ensure we can print smt terms
///   which are nested arbitrarily deeply without risk of exceeding the maximum
///   depth of the call stack.
/// \details
///   The set of `visit` functions push functions to `output_stack`,
///   which capture the value to be printed. When called these functions may
///   either print to the output stream or push further functions to the stack
///   in the case of nodes in the tree which have child nodes which also need to
///   be printed.
///   The `push_output(s)` functions exist as convenience functions to allow
///   pushing the capturing functions to the stack in the reverse order required
///   for printing, whilst keeping the visit functions easier to read by keeping
///   the outputs in reading order and separating the capturing code.
class smt_term_to_string_convertert : private smt_term_const_downcast_visitort
{
private:
  using output_functiont = std::function<void(std::ostream &)>;
  std::stack<output_functiont> output_stack;

  static output_functiont make_output_function(const std::string &output);
  static output_functiont make_output_function(const smt_sortt &output);
  output_functiont make_output_function(const smt_termt &output);
  output_functiont make_output_function(
    const std::vector<std::reference_wrapper<const smt_termt>> &output);

  /// \brief Single argument version of `push_outputs`.
  template <typename outputt>
  void push_output(outputt &&output);

  /// \brief Base case for the recursive `push_outputs` function template below.
  void push_outputs();

  /// \brief Pushes outputting functions to the output_stack for each of the
  ///   output values provided. This variadic template supports any (compile
  ///   time fixed) number of output arguments.
  /// \details The arguments are pushed in order from right to left, so that
  ///   they are subsequently in left to right order when popped off the stack.
  ///   The types of argument supported are those supported by the overloads of
  ///   the `make_output_function` function.
  /// \note This is implemented recursively, but does not risk exceeding the
  ///   maximum depth of the call stack. This is because the number of times it
  ///   recurses depends only on the number of arguments supplied in the source
  ///   code at compile time.
  template <typename outputt, typename... outputst>
  void push_outputs(outputt &&output, outputst &&... outputs);

  smt_term_to_string_convertert() = default;

  void visit(const smt_bool_literal_termt &bool_literal) override;
  void visit(const smt_identifier_termt &identifier_term) override;
  void visit(const smt_bit_vector_constant_termt &bit_vector_constant) override;
  void
  visit(const smt_function_application_termt &function_application) override;

public:
  /// \brief This function is complete the external interface to this class. All
  ///   construction of this class and printing of terms should be carried out
  ///   via this function.
  static std::ostream &convert(std::ostream &os, const smt_termt &term);
};

smt_term_to_string_convertert::output_functiont
smt_term_to_string_convertert::make_output_function(const std::string &output)
{
  // `output` must be captured by value to avoid dangling references.
  return [output](std::ostream &os) { os << output; };
}

smt_term_to_string_convertert::output_functiont
smt_term_to_string_convertert::make_output_function(const smt_sortt &output)
{
  return [=](std::ostream &os) { os << output; };
}

smt_term_to_string_convertert::output_functiont
smt_term_to_string_convertert::make_output_function(const smt_termt &output)
{
  return [=](std::ostream &os) { output.accept(*this); };
}

smt_term_to_string_convertert::output_functiont
smt_term_to_string_convertert::make_output_function(
  const std::vector<std::reference_wrapper<const smt_termt>> &outputs)
{
  return [=](std::ostream &os) {
    for(const auto &output : make_range(outputs.rbegin(), outputs.rend()))
    {
      push_outputs(" ", output.get());
    }
  };
}

template <typename outputt>
void smt_term_to_string_convertert::push_output(outputt &&output)
{
  output_stack.push(make_output_function(std::forward<outputt>(output)));
}

void smt_term_to_string_convertert::push_outputs()
{
}

template <typename outputt, typename... outputst>
void smt_term_to_string_convertert::push_outputs(
  outputt &&output,
  outputst &&... outputs)
{
  push_outputs(std::forward<outputst>(outputs)...);
  push_output(std::forward<outputt>(output));
}

void smt_term_to_string_convertert::visit(
  const smt_bool_literal_termt &bool_literal)
{
  push_output(bool_literal.value() ? "true" : "false");
}

void smt_term_to_string_convertert::visit(
  const smt_identifier_termt &identifier_term)
{
  push_outputs(
    "|", smt2_convt::convert_identifier(identifier_term.identifier()), "|");
}

void smt_term_to_string_convertert::visit(
  const smt_bit_vector_constant_termt &bit_vector_constant)
{
  auto value = integer2string(bit_vector_constant.value());
  auto bit_width = std::to_string(bit_vector_constant.get_sort().bit_width());
  push_outputs("(_ bv", std::move(value), " ", std::move(bit_width), ")");
}

void smt_term_to_string_convertert::visit(
  const smt_function_application_termt &function_application)
{
  const auto &id = function_application.function_identifier();
  auto arguments = function_application.arguments();
  push_outputs("(", id, std::move(arguments), ")");
}

std::ostream &
smt_term_to_string_convertert::convert(std::ostream &os, const smt_termt &term)
{
  smt_term_to_string_convertert converter;
  term.accept(converter);
  while(!converter.output_stack.empty())
  {
    auto output_function = std::move(converter.output_stack.top());
    converter.output_stack.pop();
    output_function(os);
  }
  return os;
}

std::ostream &operator<<(std::ostream &os, const smt_termt &term)
{
  return smt_term_to_string_convertert::convert(os, term);
}

std::string smt_to_smt2_string(const smt_termt &term)
{
  std::stringstream ss;
  ss << term;
  return ss.str();
}

class smt_option_to_string_convertert
  : public smt_option_const_downcast_visitort
{
protected:
  std::ostream &os;

public:
  explicit smt_option_to_string_convertert(std::ostream &os) : os(os)
  {
  }

  void visit(const smt_option_produce_modelst &produce_models) override
  {
    os << ":produce-models " << (produce_models.setting() ? "true" : "false");
  }
};

std::ostream &operator<<(std::ostream &os, const smt_optiont &option)
{
  option.accept(smt_option_to_string_convertert{os});
  return os;
}

std::string smt_to_smt2_string(const smt_optiont &option)
{
  std::stringstream ss;
  ss << option;
  return ss.str();
}

class smt_logic_to_string_convertert : public smt_logic_const_downcast_visitort
{
protected:
  std::ostream &os;

public:
  explicit smt_logic_to_string_convertert(std::ostream &os) : os(os)
  {
  }

#define LOGIC_ID(the_id, the_name)                                             \
  void visit(const smt_logic_##the_id##t &) override                           \
  {                                                                            \
    os << #the_name;                                                           \
  }
#include "smt_logics.def"
#undef LOGIC_ID
};

std::ostream &operator<<(std::ostream &os, const smt_logict &logic)
{
  logic.accept(smt_logic_to_string_convertert{os});
  return os;
}

std::string smt_to_smt2_string(const smt_logict &logic)
{
  std::stringstream ss;
  ss << logic;
  return ss.str();
}

class smt_command_to_string_convertert
  : public smt_command_const_downcast_visitort
{
protected:
  std::ostream &os;

public:
  explicit smt_command_to_string_convertert(std::ostream &os) : os(os)
  {
  }

  void visit(const smt_assert_commandt &assert) override
  {
    os << "(assert " << assert.condition() << ")";
  }

  void visit(const smt_check_sat_commandt &check_sat) override
  {
    os << "(check-sat)";
  }

  void visit(const smt_declare_function_commandt &declare_function) override
  {
    os << "(declare-fun " << declare_function.identifier() << " (";
    const auto parameter_sorts = declare_function.parameter_sorts();
    join_strings(os, parameter_sorts.begin(), parameter_sorts.end(), ' ');
    os << ") " << declare_function.return_sort() << ")";
  }

  void visit(const smt_define_function_commandt &define_function) override
  {
    os << "(define-fun " << define_function.identifier() << " (";
    const auto parameters = define_function.parameters();
    join_strings(
      os,
      parameters.begin(),
      parameters.end(),
      " ",
      [](const smt_identifier_termt &identifier) {
        return "(" + smt_to_smt2_string(identifier) + " " +
               smt_to_smt2_string(identifier.get_sort()) + ")";
      });
    os << ") " << define_function.return_sort() << " "
       << define_function.definition() << ")";
  }

  void visit(const smt_exit_commandt &exit) override
  {
    os << "(exit)";
  }

  void visit(const smt_get_value_commandt &get_value) override
  {
    os << "(get-value (" << get_value.descriptor() << "))";
  }

  void visit(const smt_pop_commandt &pop) override
  {
    os << "(pop " << pop.levels() << ")";
  }

  void visit(const smt_push_commandt &push) override
  {
    os << "(push " << push.levels() << ")";
  }

  void visit(const smt_set_logic_commandt &set_logic) override
  {
    os << "(set-logic " << set_logic.logic() << ")";
  }

  void visit(const smt_set_option_commandt &set_option) override
  {
    os << "(set-option " << set_option.option() << ")";
  }
};

std::ostream &operator<<(std::ostream &os, const smt_commandt &command)
{
  command.accept(smt_command_to_string_convertert{os});
  return os;
}

std::string smt_to_smt2_string(const smt_commandt &command)
{
  std::stringstream ss;
  ss << command;
  return ss.str();
}
