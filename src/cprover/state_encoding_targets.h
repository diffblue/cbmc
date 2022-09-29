/*******************************************************************\

Module: State Encoding Targets

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_CPROVER_STATE_ENCODING_TARGETS_H
#define CPROVER_CPROVER_STATE_ENCODING_TARGETS_H

#include <solvers/smt2/smt2_conv.h>

#include <iosfwd>

class encoding_targett
{
public:
  virtual void annotation(const std::string &)
  {
  }

  virtual void set_to_true(source_locationt, exprt) = 0;

  void set_to_true(exprt expr)
  {
    set_to_true(source_location, std::move(expr));
  }

  void set_source_location(source_locationt __source_location)
  {
    source_location = std::move(__source_location);
  }

  virtual ~encoding_targett() = default;

protected:
  source_locationt source_location = source_locationt::nil();
};

class container_encoding_targett : public encoding_targett
{
public:
  container_encoding_targett() = default;

  using constraintst = std::vector<exprt>;
  constraintst constraints;

  void set_to_true(source_locationt source_location, exprt expr) override
  {
    if(source_location.is_not_nil())
      expr.add_source_location() = source_location;

    constraints.emplace_back(std::move(expr));
  }

protected:
  source_locationt last_source_location = source_locationt::nil();
};

static inline void operator<<(encoding_targett &target, exprt constraint)
{
  target.set_to_true(std::move(constraint));
}

static inline void
operator<<(encoding_targett &target, const container_encoding_targett &src)
{
  for(const auto &constraint : src.constraints)
    target << constraint;
}

class state_encoding_smt2_convt : public smt2_convt
{
public:
  state_encoding_smt2_convt(const namespacet &ns, std::ostream &_out)
    : smt2_convt(ns, "", "cprover", "", smt2_convt::solvert::GENERIC, _out)

  {
    use_array_of_bool = true;
    use_as_const = true;
    add_converters();
  }

  void add_converters();
};

class smt2_encoding_targett : public encoding_targett
{
public:
  smt2_encoding_targett(const namespacet &ns, std::ostream &_out)
    : out(_out), smt2_conv(ns, _out)
  {
  }

  ~smt2_encoding_targett()
  {
    // finish the conversion to SMT-LIB2
    smt2_conv();
  }

  void set_to_true(source_locationt, exprt expr) override
  {
    smt2_conv.set_to_true(std::move(expr));
  }

  void annotation(const std::string &text) override
  {
    if(text.empty())
      out << '\n';
    else
      out << ';' << ' ' << text << '\n';
  }

protected:
  std::ostream &out;
  state_encoding_smt2_convt smt2_conv;

  void add_converters();
};

class ascii_encoding_targett : public encoding_targett
{
public:
  explicit ascii_encoding_targett(std::ostream &_out) : out(_out)
  {
  }

  void set_to_true(source_locationt, exprt) override;

  void annotation(const std::string &text) override
  {
    out << text << '\n';
  }

protected:
  std::ostream &out;
  std::size_t counter = 0;
};

#endif // CPROVER_CPROVER_STATE_ENCODING_TARGETS_H
