// Author: Diffblue Ltd.

#include <solvers/smt2_incremental/smt_to_string.h>

#include <solvers/smt2/smt2_conv.h>
#include <solvers/smt2_incremental/smt_sorts.h>
#include <solvers/smt2_incremental/smt_terms.h>

#include <util/range.h>

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

std::string smt_to_string(const smt_sortt &sort)
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
  void visit(const smt_not_termt &not_term) override;
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
  // `output` can be safely captured by reference, because no sorts are copied
  // or constructed as part of conversion to string.
  return [&](std::ostream &os) { os << output; };
}

smt_term_to_string_convertert::output_functiont
smt_term_to_string_convertert::make_output_function(const smt_termt &output)
{
  // `output` can be safely captured by reference, because no terms are copied
  // or constructed as part of conversion to string.
  return [&](std::ostream &os) { output.accept(*this); };
}

smt_term_to_string_convertert::output_functiont
smt_term_to_string_convertert::make_output_function(
  const std::vector<std::reference_wrapper<const smt_termt>> &outputs)
{
  // `outputs` must be captured by value to avoid a dangling reference to the
  // vector. The elements in the vector are not at risk of dangling as the
  // lifetime of the terms to which they refer is at least as long as the
  // execution of the overall printing algorithm.
  return [&, outputs](std::ostream &os) {
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

void smt_term_to_string_convertert::visit(const smt_not_termt &not_term)
{
  push_outputs("(not ", not_term.operand(), ")");
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

std::string smt_to_string(const smt_termt &term)
{
  std::stringstream ss;
  ss << term;
  return ss.str();
}
