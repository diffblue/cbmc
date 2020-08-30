/*******************************************************************\

Module: Horn-clause Encoding

Author: Daniel Kroening

Date: June 2015

\*******************************************************************/

/// \file
/// Horn-clause Encoding

#include "horn_encoding.h"

#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/string_utils.h>

#include <solvers/decision_procedure.h>
#include <solvers/smt2/smt2_conv.h>

#include <algorithm>
#include <functional>
#include <ostream>

class encoding_targett
{
public:
  virtual void set_to_true(exprt) = 0;
  virtual std::ostream &comment() = 0;

  virtual ~encoding_targett()
  {
  }

  encoding_targett &
  operator<<(const std::function<void(encoding_targett &)> &encoder)
  {
    encoder(*this);
    return *this;
  }
};

std::set<symbol_exprt> signature(
  const goto_functiont &function,
  const namespacet &ns,
  bool pre,
  bool post,
  bool locals)
{
  std::set<symbol_exprt> all_symbols;
  std::set<symbol_exprt> decl_symbols;

  for(auto &instruction : function.body.instructions)
  {
    switch(instruction.type)
    {
    case GOTO:
    case ASSUME:
    case ASSERT:
      find_symbols(instruction.get_condition(), all_symbols);
      break;

    case DECL:
      find_symbols(instruction.get_decl(), decl_symbols);
      break;

    case OTHER:
      find_symbols(instruction.get_other(), all_symbols);
      break;

    case RETURN:
      find_symbols(instruction.get_return(), all_symbols);
      break;

    case ASSIGN:
      find_symbols(instruction.get_assign(), all_symbols);
      break;

    case FUNCTION_CALL:
      find_symbols(instruction.get_function_call(), all_symbols);
      break;

    case DEAD:
    case NO_INSTRUCTION_TYPE:
    case START_THREAD:
    case END_THREAD:
    case LOCATION:
    case SKIP:
    case ATOMIC_BEGIN:
    case ATOMIC_END:
    case THROW:
    case CATCH:
    case INCOMPLETE_GOTO:
    case END_FUNCTION:;
    }
  }

  std::set<symbol_exprt> result;

  // static lifetime
  if(pre || post)
  {
    for(auto &s : all_symbols)
    {
      auto &symbol = ns.lookup(s);
      if(symbol.is_state_var)
      {
        if(symbol.is_static_lifetime)
          result.insert(symbol.symbol_expr());
      }
    }
  }

  // parameters
  if(pre || locals)
  {
    for(auto &parameter : function.parameter_identifiers)
    {
      if(!parameter.empty())
      {
        auto &symbol = ns.lookup(parameter);
        result.insert(symbol.symbol_expr());
      }
    }
  }

  // locals
  if(locals)
  {
    for(auto &s : decl_symbols)
    {
      auto &symbol = ns.lookup(s);
      result.insert(symbol.symbol_expr());
    }
  }

  return result;
}

mathematical_function_typet
predicate_type(const std::set<symbol_exprt> &symbols)
{
  mathematical_function_typet::domaint domain;

  for(auto &s : symbols)
    domain.push_back(s.type());

  return mathematical_function_typet(domain, bool_typet());
}

exprt forall(const std::set<symbol_exprt> &quantified_variables, exprt expr)
{
  for(auto &v : quantified_variables)
    expr = forall_exprt(v, expr);

  return expr;
}

exprt apply(
  const exprt &state_predicate,
  const std::set<symbol_exprt> &state_variables)
{
  function_application_exprt::argumentst arguments;

  for(auto &v : state_variables)
    arguments.push_back(v);

  return function_application_exprt(state_predicate, arguments);
}

exprt assignment(
  const code_assignt &src,
  const exprt &state_predicate,
  const std::set<symbol_exprt> &state_variables)
{
  function_application_exprt::argumentst arguments;

  for(auto &v : state_variables)
  {
    if(src.lhs() == v)
      arguments.push_back(src.rhs());
    else
      arguments.push_back(v);
  }

  return function_application_exprt(state_predicate, arguments);
}

symbol_exprt state_predicate(
  const irep_idt function_identifier,
  const goto_programt::instructiont &instruction,
  const std::string &prefix,
  const typet &local_state_type)
{
  const std::string suffix = "." + id2string(function_identifier) + "." +
                             std::to_string(instruction.location_number);
  return symbol_exprt(prefix + suffix, local_state_type);
}

exprt state_implication(
  const exprt &a,
  const std::set<symbol_exprt> &a_variables,
  const exprt &b,
  const std::set<symbol_exprt> &b_variables)
{
  std::set<symbol_exprt> variables;

  std::set_union(
    a_variables.begin(),
    a_variables.end(),
    b_variables.begin(),
    b_variables.end(),
    std::inserter(variables, variables.begin()));

  return forall(
    variables, implies_exprt(apply(a, a_variables), apply(b, b_variables)));
}

/// encoding of one function
std::function<void(encoding_targett &)> horn_encoding(
  irep_idt identifier,
  const goto_functiont &function,
  const namespacet &ns)
{
  return [identifier, &function, &ns](encoding_targett &target) {
    target.comment() << "Encoding of function " << identifier;

    const auto precondition_signature =
      signature(function, ns, true, false, false);

    const auto postcondition_signature =
      signature(function, ns, false, true, false);

    const auto local_state_signature =
      signature(function, ns, true, true, true);

    const auto local_state_type = predicate_type(local_state_signature);

    auto &comment = target.comment();
    comment << "Local state:";
    for(auto &v : local_state_signature)
      comment << ' ' << format(v);

    // Predicates over the state:
    // * a precondition -- pre.f
    // * a postcondition -- post.f
    // * two invariants per location -- pre.f.loc and post.f.loc

    // the precondition implies the 'entry node'
    if(!function.body.empty())
    {
      const std::string suffix = "." + id2string(identifier);
      auto function_pre =
        symbol_exprt("pre" + suffix, predicate_type(precondition_signature));

      auto pre_front = state_predicate(
        identifier,
        function.body.instructions.front(),
        "pre",
        local_state_type);
      target.set_to_true(state_implication(
        function_pre,
        precondition_signature,
        pre_front,
        local_state_signature));
    }

    for(auto &instruction : function.body.instructions)
    {
      target.comment() << instruction.source_location << ' '
                       << instruction.type;

      const auto pre =
        state_predicate(identifier, instruction, "pre", local_state_type);
      const auto post =
        state_predicate(identifier, instruction, "post", local_state_type);

      // link the pre-state to the post-states of the incoming edges
      std::vector<exprt> disjuncts;

      for(auto e : instruction.incoming_edges)
      {
        std::string e_prefix;

        // is the incoming edge coming from a GOTO?
        if(e->is_goto())
        {
          // taken or not taken?
          if(std::next(e)->location_number == instruction.location_number)
            e_prefix = "post-not-taken";
          else
            e_prefix = "post-taken";
        }
        else
          e_prefix = "post";

        auto e_pred =
          state_predicate(identifier, *e, e_prefix, local_state_type);
        disjuncts.push_back(equal_exprt(pre, e_pred));
      }

      if(!disjuncts.empty())
        target.set_to_true(disjunction(std::move(disjuncts)));

      // encode the post-condition of the instruction
      switch(instruction.type)
      {
      case ASSUME:
        // ∀X. pre(X) ∧ cond(X) ⇒ post(X)
        target.set_to_true(forall(
          local_state_signature,
          implies_exprt(and_exprt(pre, instruction.get_condition()), post)));
        break;

      case ASSERT:
        // ∀X. pre(X) ⇒ cond(X)
        target.set_to_true(forall(
          local_state_signature,
          implies_exprt(apply(pre, local_state_signature), instruction.get_condition())));
        // post = pre
        target.set_to_true(equal_exprt(post, pre));
        break;

      case ASSIGN:
        // lhs = rhs
        //   ∀X pre(X) ⇒ post(X[lhs:=rhs[X]])
        target.set_to_true(forall(
          local_state_signature,
          implies_exprt(
            apply(pre, local_state_signature),
            assignment(
              instruction.get_assign(), post, local_state_signature))));
        break;

      case GOTO:
        // distinguish 'branch taken' and 'branch not taken'
        {
          const auto post_taken = state_predicate(
            identifier, instruction, "post-taken", local_state_type);

          target.set_to_true(forall(
            local_state_signature,
            implies_exprt(
              and_exprt(pre, instruction.get_condition()), post_taken)));

          const auto post_not_taken = state_predicate(
            identifier, instruction, "post-not-taken", local_state_type);

          target.set_to_true(forall(
            local_state_signature,
            implies_exprt(
              and_exprt(pre, not_exprt(instruction.get_condition())),
              post_not_taken)));
        }
        break;

      case FUNCTION_CALL:
        // post = pre, TBD
        target.set_to_true(equal_exprt(post, pre));
        break;

      case OTHER:
      case THROW:
      case CATCH:
      case DECL:
      case DEAD:
      case ATOMIC_BEGIN:
      case ATOMIC_END:
      case SKIP:
      case START_THREAD:
      case END_THREAD:
      case LOCATION:
      case END_FUNCTION:
        // post = pre
        target.set_to_true(equal_exprt(post, pre));
        break;

      case NO_INSTRUCTION_TYPE:
        DATA_INVARIANT(false, "horn_encoding got NO_INSTRUCTION_TYPE");
        break;

      case INCOMPLETE_GOTO:
        DATA_INVARIANT(false, "horn_encoding got INCOMPLETE_GOTO");
        break;

      case RETURN:
        // we ran remove_returns
        DATA_INVARIANT(false, "horn_encoding got RETURN");
        break;
      }
    }

    // the 'exit node' implies the function's postcondition
    if(!function.body.empty())
    {
      target.comment() << "postcondition of the function";
      const std::string suffix = "." + id2string(identifier);
      auto function_post =
        symbol_exprt("post" + suffix, predicate_type(postcondition_signature));

      auto post_back = state_predicate(
        identifier,
        function.body.instructions.back(),
        "post",
        local_state_type);
      target.set_to_true(state_implication(
        post_back,
        local_state_signature,
        function_post,
        postcondition_signature));
    }
  };
}

/// encoding of an entire program
std::function<void(encoding_targett &)> horn_encoding(const goto_modelt &model)
{
  return [&model](encoding_targett &target) {
    const namespacet ns(model.symbol_table);
    // we encode with function granularity
    for(auto &f : model.goto_functions.function_map)
    {
      target << horn_encoding(f.first, f.second, ns);
    }
  };
}

class text_encoding_targett : public encoding_targett
{
public:
  explicit text_encoding_targett(std::ostream &__out) : out(__out)
  {
  }

  void set_to_true(exprt e) override
  {
    emit_comments();
    out << format(e) << '\n';
  }

  std::ostream &comment() override
  {
    emit_comments();
    return comment_buffer;
  }

  ~text_encoding_targett()
  {
    emit_comments();
  }

protected:
  std::ostream &out;
  std::ostringstream comment_buffer;

  void emit_comments()
  {
    auto comments = comment_buffer.str();
    if(!comments.empty())
    {
      const auto lines = split_string(comments, '\n');
      for(auto &line : lines)
        out << "; " << line << '\n';
      comment_buffer = std::ostringstream();
    }
  }
};

class smt2_encoding_targett : public encoding_targett
{
public:
  smt2_encoding_targett(std::ostream &__out, const namespacet &__ns)
    : out(__out),
      smt2_conv(__ns, "", "", "HORN", smt2_convt::solvert::Z3, __out),
      comment_stream(&null_streambuf)
  {
  }

  void set_to_true(exprt e) override
  {
    smt2_conv.set_to_true(e);
  }

  std::ostream &comment() override
  {
    // drop
    return comment_stream;
  }

protected:
  std::ostream &out;
  smt2_convt smt2_conv;
  std::ostream comment_stream;

  class dev0_buffer : public std::streambuf
  {
    std::streamsize xsputn(const char *s, std::streamsize n) override
    {
      return n;
    }
    int overflow(int c) override
    {
      return c;
    }
  } null_streambuf;
};

void horn_encoding(
  const goto_modelt &model,
  horn_formatt format,
  std::ostream &out)
{
  switch(format)
  {
  case horn_formatt::ASCII:
  {
    text_encoding_targett target(out);
    target << horn_encoding(model);
  }
  break;

  case horn_formatt::SMT2:
  {
    const namespacet ns(model.symbol_table);
    smt2_encoding_targett target(out, ns);
    target << horn_encoding(model);
  }
  break;
  }
}
