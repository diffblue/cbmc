/*******************************************************************\

Module: Horn-clause Encoding

Author: Daniel Kroening

Date: June 2015

\*******************************************************************/

/// \file
/// Horn-clause Encoding

#include "horn_encoding.h"

#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/format_expr.h>
#include <util/mathematical_expr.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/replace_symbol.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <goto-programs/goto_model.h>

#include <solvers/smt2/smt2_conv.h>

#include <algorithm>
#include <ostream>
#include <unordered_set>

class state_typet : public typet
{
public:
  state_typet() : typet(ID_state)
  {
  }
};

static inline mathematical_function_typet state_predicate_type()
{
  return mathematical_function_typet({state_typet()}, bool_typet());
}

static inline symbol_exprt state_expr()
{
  return symbol_exprt(u8"\u03c2", state_typet());
}

class evaluate_exprt : public binary_exprt
{
public:
  evaluate_exprt(exprt state, exprt address, typet type)
    : binary_exprt(
        std::move(state),
        ID_evaluate,
        std::move(address),
        std::move(type))
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }
};

/// \brief Cast an exprt to a \ref evaluate_exprt
///
/// \a expr must be known to be \ref evaluate_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref evaluate_exprt
inline const evaluate_exprt &to_evaluate_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_evaluate);
  const evaluate_exprt &ret = static_cast<const evaluate_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_evaluate_expr(const exprt &)
inline evaluate_exprt &to_evaluate_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_evaluate);
  evaluate_exprt &ret = static_cast<evaluate_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class update_state_exprt : public ternary_exprt
{
public:
  update_state_exprt(exprt state, exprt address, exprt new_value)
    : ternary_exprt(
        ID_update_state,
        std::move(state),
        std::move(address),
        std::move(new_value),
        state_typet())
  {
    // PRECONDITION(this->state().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  const exprt &new_value() const
  {
    return op2();
  }
};

/// \brief Cast an exprt to a \ref update_state_exprt
///
/// \a expr must be known to be \ref update_state_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref update_state_exprt
inline const update_state_exprt &to_update_state_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_update_state);
  const update_state_exprt &ret = static_cast<const update_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

/// \copydoc to_update_state_expr(const exprt &)
inline update_state_exprt &to_update_state_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_update_state);
  update_state_exprt &ret = static_cast<update_state_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

class allocate_exprt : public ternary_exprt
{
public:
  allocate_exprt(exprt state, exprt address, exprt size)
    : ternary_exprt(
        ID_allocate,
        std::move(state),
        std::move(address),
        std::move(size),
        state_typet())
  {
    PRECONDITION(this->state().type().id() == ID_state);
    PRECONDITION(this->address().type().id() == ID_pointer);
  }

  const exprt &state() const
  {
    return op0();
  }

  exprt &state()
  {
    return op0();
  }

  const exprt &address() const
  {
    return op1();
  }

  const exprt &size() const
  {
    return op2();
  }
};

/// \brief Cast an exprt to a \ref allocate_exprt
///
/// \a expr must be known to be \ref allocate_exprt.
///
/// \param expr: Source expression
/// \return Object of type \ref allocate_exprt
inline const allocate_exprt &to_allocate_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_allocate);
  const allocate_exprt &ret = static_cast<const allocate_exprt &>(expr);
  validate_expr(ret);
  return ret;
}

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

class smt2_encoding_targett : public encoding_targett
{
public:
  smt2_encoding_targett(const namespacet &ns, std::ostream &_out)
    : out(_out),
      smt2_conv(ns, "", "cprover", "", smt2_convt::solvert::GENERIC, _out)
  {
    smt2_conv.use_array_of_bool = true;
    smt2_conv.use_as_const = true;
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
  smt2_convt smt2_conv;
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

static void find_variables_rec(
  const exprt &src,
  std::unordered_set<symbol_exprt, irep_hash> &result)
{
  if(src.id() == ID_object_address)
    result.insert(to_object_address_expr(src).object_expr());
  else
  {
    for(auto &op : src.operands())
      find_variables_rec(op, result);
  }
}

class state_encodingt
{
public:
  explicit state_encodingt(const goto_functionst &__goto_functions)
    : goto_functions(__goto_functions)
  {
  }

  void operator()(
    const goto_functionst::function_mapt::const_iterator,
    encoding_targett &);

  void encode(
    const goto_functiont &,
    const std::string &state_prefix,
    const std::string &annotation,
    const symbol_exprt &entry_state,
    const exprt &return_lhs,
    encoding_targett &);

protected:
  using loct = goto_programt::const_targett;
  const goto_functionst &goto_functions;

  symbol_exprt out_state_expr(loct) const;
  symbol_exprt state_expr_with_suffix(loct, const std::string &suffix) const;
  symbol_exprt out_state_expr(loct, bool taken) const;
  symbol_exprt in_state_expr(loct) const;
  std::vector<symbol_exprt> incoming_symbols(loct) const;
  exprt evaluate_expr(loct, const exprt &, const exprt &) const;
  exprt evaluate_expr_rec(
    loct,
    const exprt &,
    const exprt &,
    const std::unordered_set<symbol_exprt, irep_hash> &) const;
  exprt replace_nondet_rec(
    loct,
    const exprt &,
    std::vector<symbol_exprt> &nondet_symbols) const;
  exprt evaluate_expr(loct, const exprt &) const;
  exprt address_rec(loct, const exprt &, exprt) const;
  static exprt state_lambda_expr(exprt);
  exprt forall_states_expr(loct, exprt) const;
  exprt forall_states_expr(loct, exprt, exprt) const;
  void setup_incoming(const goto_functiont &);
  exprt assignment_constraint(loct, exprt lhs, exprt rhs) const;
  void function_call(goto_programt::const_targett, encoding_targett &);
  void function_call_symbol(goto_programt::const_targett, encoding_targett &);

  std::string state_prefix;
  std::string annotation;
  loct first_loc;
  symbol_exprt entry_state = symbol_exprt(irep_idt(), typet());
  exprt return_lhs = nil_exprt();
  using incomingt = std::map<loct, std::vector<loct>>;
  incomingt incoming;
};

symbol_exprt state_encodingt::out_state_expr(loct loc) const
{
  return state_expr_with_suffix(loc, "");
}

symbol_exprt state_encodingt::state_expr_with_suffix(
  loct loc,
  const std::string &suffix) const
{
  irep_idt identifier =
    state_prefix + std::to_string(loc->location_number) + suffix;
  return symbol_exprt(identifier, state_predicate_type());
}

symbol_exprt state_encodingt::out_state_expr(loct loc, bool taken) const
{
  return state_expr_with_suffix(loc, taken ? "T" : "");
}

std::vector<symbol_exprt> state_encodingt::incoming_symbols(loct loc) const
{
  auto incoming_it = incoming.find(loc);

  DATA_INVARIANT(incoming_it != incoming.end(), "incoming is complete");

  std::vector<symbol_exprt> symbols;
  symbols.reserve(incoming_it->second.size());

  for(auto &loc_in : incoming_it->second)
  {
    std::string suffix;

    // conditional jump from loc_in to loc?
    if(
      loc_in->is_goto() && !loc_in->condition().is_true() &&
      loc != std::next(loc_in))
    {
      suffix = "T";
    }

    symbols.push_back(state_expr_with_suffix(loc_in, suffix));
  }

  return symbols;
}

symbol_exprt state_encodingt::in_state_expr(loct loc) const
{
  if(loc == first_loc)
    return entry_state;

  auto incoming_symbols = this->incoming_symbols(loc);

  if(incoming_symbols.size() == 1)
    return incoming_symbols.front();
  else
    return state_expr_with_suffix(loc, "in");
}

exprt state_encodingt::evaluate_expr(
  loct loc,
  const exprt &state,
  const exprt &what) const
{
  return evaluate_expr_rec(loc, state, what, {});
}

exprt state_encodingt::replace_nondet_rec(
  loct loc,
  const exprt &what,
  std::vector<symbol_exprt> &nondet_symbols) const
{
  if(what.id() == ID_side_effect)
  {
    auto &side_effect = to_side_effect_expr(what);
    auto statement = side_effect.get_statement();
    if(statement == ID_nondet)
    {
      irep_idt identifier =
        "nondet::" + state_prefix + std::to_string(loc->location_number);
      auto symbol = symbol_exprt(identifier, side_effect.type());
      nondet_symbols.push_back(symbol);
      return std::move(symbol);
    }
    else
      return what; // leave it
  }
  else
  {
    exprt tmp = what;
    for(auto &op : tmp.operands())
      op = replace_nondet_rec(loc, op, nondet_symbols);
    return tmp;
  }
}

exprt state_encodingt::evaluate_expr_rec(
  loct loc,
  const exprt &state,
  const exprt &what,
  const std::unordered_set<symbol_exprt, irep_hash> &bound_symbols) const
{
  PRECONDITION(state.type().id() == ID_state);

  if(what.id() == ID_symbol)
  {
    const auto &symbol_expr = to_symbol_expr(what);

    if(bound_symbols.find(symbol_expr) == bound_symbols.end())
    {
      return evaluate_exprt(state, address_rec(loc, state, what), what.type());
    }
    else
      return what; // leave as is
  }
  else if(
    what.id() == ID_dereference || what.id() == ID_member ||
    what.id() == ID_index)
  {
    return evaluate_exprt(state, address_rec(loc, state, what), what.type());
  }
  else if(what.id() == ID_forall || what.id() == ID_exists)
  {
    auto new_quantifier_expr = to_quantifier_expr(what); // copy
    auto new_bound_symbols = bound_symbols;              // copy

    for(const auto &v : new_quantifier_expr.variables())
      new_bound_symbols.insert(v);

    new_quantifier_expr.where() = evaluate_expr_rec(
      loc, state, new_quantifier_expr.where(), new_bound_symbols);

    return std::move(new_quantifier_expr);
  }
  else if(what.id() == ID_address_of)
  {
    const auto &object = to_address_of_expr(what).object();
    return address_rec(loc, state, object);
  }
  else if(what.id() == ID_r_ok || what.id() == ID_w_ok || what.id() == ID_rw_ok)
  {
    // we need to add the state
    const auto &r_or_w_ok_expr = to_r_or_w_ok_expr(what);
    auto pointer =
      evaluate_expr_rec(loc, state, r_or_w_ok_expr.pointer(), bound_symbols);
    auto size =
      evaluate_expr_rec(loc, state, r_or_w_ok_expr.size(), bound_symbols);
    return ternary_exprt(what.id(), state, pointer, size, what.type());
  }
  else
  {
    exprt tmp = what;
    for(auto &op : tmp.operands())
      op = evaluate_expr_rec(loc, state, op, bound_symbols);
    return tmp;
  }
}

exprt state_encodingt::evaluate_expr(loct loc, const exprt &what) const
{
  return evaluate_expr(loc, in_state_expr(loc), what);
}

exprt state_encodingt::state_lambda_expr(exprt what)
{
  return lambda_exprt({state_expr()}, std::move(what));
}

exprt state_encodingt::forall_states_expr(loct loc, exprt what) const
{
  return forall_exprt(
    {state_expr()},
    implies_exprt(
      function_application_exprt(in_state_expr(loc), {state_expr()}),
      std::move(what)));
}

exprt state_encodingt::forall_states_expr(loct loc, exprt condition, exprt what)
  const
{
  return forall_exprt(
    {state_expr()},
    implies_exprt(
      and_exprt(
        function_application_exprt(in_state_expr(loc), {state_expr()}),
        std::move(condition)),
      std::move(what)));
}

exprt state_encodingt::address_rec(loct loc, const exprt &state, exprt expr)
  const
{
  if(expr.id() == ID_symbol)
  {
    if(expr.type().id() == ID_array)
    {
      const auto &element_type = to_array_type(expr.type()).element_type();
      return object_address_exprt(
        to_symbol_expr(expr), pointer_type(element_type));
    }
    else
      return object_address_exprt(to_symbol_expr(expr));
  }
  else if(expr.id() == ID_member)
  {
    auto compound = to_member_expr(expr).struct_op();
    auto compound_address = address_rec(loc, state, std::move(compound));
    auto component_name = to_member_expr(expr).get_component_name();

    if(expr.type().id() == ID_array)
    {
      const auto &element_type = to_array_type(expr.type()).element_type();
      return field_address_exprt(
        std::move(compound_address),
        component_name,
        pointer_type(element_type));
    }
    else
    {
      return field_address_exprt(
        std::move(compound_address), component_name, pointer_type(expr.type()));
    }
  }
  else if(expr.id() == ID_index)
  {
    auto array = to_index_expr(expr).array();
    auto index_evaluated =
      evaluate_expr(loc, state, to_index_expr(expr).index());
    auto array_address = address_rec(loc, state, std::move(array));
    return element_address_exprt(
      std::move(array_address), std::move(index_evaluated));
  }
  else if(expr.id() == ID_dereference)
    return evaluate_expr(loc, state, to_dereference_expr(expr).pointer());
  else if(expr.id() == ID_string_constant)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do string literals", expr.source_location());
  }
  else if(expr.id() == ID_array)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do array literals", expr.source_location());
  }
  else if(expr.id() == ID_union)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do union literals", expr.source_location());
  }
  else
    return nil_exprt();
}

exprt state_encodingt::assignment_constraint(loct loc, exprt lhs, exprt rhs)
  const
{
  auto s = state_expr();

  auto address = address_rec(loc, s, lhs);

  exprt rhs_evaluated = evaluate_expr(loc, s, rhs);

  std::vector<symbol_exprt> nondet_symbols;
  exprt new_value = replace_nondet_rec(loc, rhs_evaluated, nondet_symbols);

  auto new_state = update_state_exprt(s, address, new_value);

  return forall_states_expr(
    loc, function_application_exprt(out_state_expr(loc), {new_state}));
}

void state_encodingt::setup_incoming(const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
    incoming[it];

  forall_goto_program_instructions(it, goto_function.body)
  {
    if(it->is_goto())
      incoming[it->get_target()].push_back(it);
  }

  forall_goto_program_instructions(it, goto_function.body)
  {
    auto next = std::next(it);
    if(it->is_goto() && it->condition().is_true())
    {
    }
    else if(next != goto_function.body.instructions.end())
    {
      incoming[next].push_back(it);
    }
  }
}

static exprt simplifying_not(exprt src)
{
  if(src.id() == ID_not)
    return to_not_expr(src).op();
  else
    return not_exprt(src);
}

static bool has_contract(const code_with_contract_typet &contract)
{
  return !contract.assigns().empty() || !contract.requires().empty() ||
         !contract.ensures().empty();
}

void state_encodingt::function_call_symbol(
  goto_programt::const_targett loc,
  encoding_targett &dest)
{
  const auto &function = to_symbol_expr(loc->call_function());
  const auto &type = to_code_type(function.type());
  auto identifier = function.get_identifier();

  auto new_annotation = annotation + u8" \u2192 " + id2string(identifier);
  dest.annotation(new_annotation);

  // malloc is special-cased
  if(identifier == "malloc")
  {
    auto state = state_expr();
    PRECONDITION(loc->call_arguments().size() == 1);
    auto size_evaluated = evaluate_expr(loc, state, loc->call_arguments()[0]);

    auto lhs_address = address_rec(loc, state, loc->call_lhs());
    exprt new_state = ternary_exprt(
      ID_allocate, state, lhs_address, size_evaluated, state_typet());
    dest << forall_states_expr(
      loc, function_application_exprt(out_state_expr(loc), {new_state}));
    return;
  }

  // Find the function
  auto f = goto_functions.function_map.find(identifier);
  if(f == goto_functions.function_map.end())
    DATA_INVARIANT(false, "failed find function in function_map");

  // Do we have a function body?
  if(!f->second.body_available())
  {
    // no function body -- do LHS assignment nondeterministically, if any
    if(loc->call_lhs().is_not_nil())
    {
      auto rhs = side_effect_expr_nondett(
        loc->call_lhs().type(), loc->source_location());
      dest << assignment_constraint(loc, loc->call_lhs(), std::move(rhs));
    }
    else
    {
      // This is a SKIP.
      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
  }

  // Evaluate the arguments of the call in the 'in state'
  exprt arguments_state = state_expr();

  for(std::size_t i = 0; i < type.parameters().size(); i++)
  {
    auto address = object_address_exprt(symbol_exprt(
      f->second.parameter_identifiers[i], type.parameters()[i].type()));
    auto argument = loc->call_arguments()[i];
    auto value = evaluate_expr(loc, state_expr(), argument);
    arguments_state = update_state_exprt(arguments_state, address, value);
  }

  // Now assign them
  auto function_entry_state = state_expr_with_suffix(loc, "Entry");
  dest << forall_states_expr(
    loc, function_application_exprt(function_entry_state, {arguments_state}));

  // now do the body, recursively
  state_encodingt body_state_encoding(goto_functions);
  auto new_state_prefix =
    state_prefix + std::to_string(loc->location_number) + ".";
  body_state_encoding.encode(
    f->second,
    new_state_prefix,
    new_annotation,
    function_entry_state,
    nil_exprt(),
    dest);

  // exit state of called function
  auto exit_loc = std::prev(f->second.body.instructions.end());
  irep_idt exit_state_identifier =
    new_state_prefix + std::to_string(exit_loc->location_number);
  auto exit_state = symbol_exprt(exit_state_identifier, state_predicate_type());

  // now link up return state
  dest << equal_exprt(out_state_expr(loc), std::move(exit_state));
}

void state_encodingt::function_call(
  goto_programt::const_targett loc,
  encoding_targett &dest)
{
  // Function pointer?
  const auto &function = loc->call_function();
  if(function.id() == ID_dereference)
  {
    // TBD.
    throw incorrect_goto_program_exceptiont(
      "can't do function pointers", loc->source_location());
  }
  else if(function.id() == ID_symbol)
  {
    function_call_symbol(loc, dest);
  }
  else
  {
    DATA_INVARIANT(
      false, "got function that's neither a symbol nor a function pointer");
  }
}

void state_encodingt::operator()(
  goto_functionst::function_mapt::const_iterator f_entry,
  encoding_targett &dest)
{
  const auto &goto_function = f_entry->second;

  if(goto_function.body.instructions.empty())
    return;

  // initial state
  auto in_state = symbol_exprt("SInitial", state_predicate_type());

  dest << forall_exprt(
    {state_expr()},
    implies_exprt(
      true_exprt(), function_application_exprt(in_state, {state_expr()})));

  auto annotation = id2string(f_entry->first);

  encode(goto_function, "S", annotation, in_state, nil_exprt(), dest);
}

void state_encodingt::encode(
  const goto_functiont &goto_function,
  const std::string &state_prefix,
  const std::string &annotation,
  const symbol_exprt &entry_state,
  const exprt &return_lhs,
  encoding_targett &dest)
{
  first_loc = goto_function.body.instructions.begin();
  this->state_prefix = state_prefix;
  this->annotation = annotation;
  this->entry_state = entry_state;
  this->return_lhs = return_lhs;

  setup_incoming(goto_function);

  // constraints for each instruction
  forall_goto_program_instructions(loc, goto_function.body)
  {
    // pass on the source code location
    dest.set_source_location(loc->source_location());

    // constraints on the incoming state
    {
      auto incoming_symbols = this->incoming_symbols(loc);

      if(incoming_symbols.size() >= 2)
      {
        auto s = state_expr();
        for(auto incoming_symbol : incoming_symbols)
        {
          dest << forall_exprt(
            {s},
            implies_exprt(
              function_application_exprt(incoming_symbol, {s}),
              function_application_exprt(in_state_expr(loc), {s})));
        }
      }
    }

    if(loc->is_assign())
    {
      auto &lhs = loc->assign_lhs();
      auto &rhs = loc->assign_rhs();

      if(lhs.type().id() == ID_array)
      {
        // skip
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else if(lhs.type().id() == ID_struct_tag)
      {
        // skip
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else if(
        lhs.id() == ID_symbol &&
        has_prefix(
          id2string(to_symbol_expr(lhs).get_identifier()), CPROVER_PREFIX) &&
        to_symbol_expr(lhs).get_identifier() != CPROVER_PREFIX "rounding_mode")
      {
        // skip for now
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else
        dest << assignment_constraint(loc, lhs, rhs);
    }
    else if(loc->is_assume())
    {
      // we produce ∅ when the assumption is false
      auto state = state_expr();
      auto condition_evaluated = evaluate_expr(loc, state, loc->condition());

      dest << forall_states_expr(
        loc,
        condition_evaluated,
        function_application_exprt(out_state_expr(loc), {state}));
    }
    else if(loc->is_goto())
    {
      // We produce ∅ when the 'other' branch is taken. Get the condition.
      const auto &condition = loc->condition();

      if(condition.is_true())
      {
        dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
      }
      else
      {
        auto state = state_expr();
        auto condition_evaluated = evaluate_expr(loc, state, condition);

        dest << forall_states_expr(
          loc,
          condition_evaluated,
          function_application_exprt(out_state_expr(loc, true), {state}));

        dest << forall_states_expr(
          loc,
          simplifying_not(condition_evaluated),
          function_application_exprt(out_state_expr(loc, false), {state}));
      }
    }
    else if(loc->is_assert())
    {
      // all assertions need to hold
      dest << forall_states_expr(
        loc, evaluate_expr(loc, state_expr(), loc->condition()));

      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
    else if(
      loc->is_skip() || loc->is_assert() || loc->is_location() ||
      loc->is_end_function() || loc->is_other())
    {
      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
    else if(loc->is_decl() || loc->is_dead())
    {
      // may wish to havoc the symbol
      dest << equal_exprt(out_state_expr(loc), in_state_expr(loc));
    }
    else if(loc->is_function_call())
    {
      function_call(loc, dest);
    }
    else if(loc->is_set_return_value())
    {
      const auto &rhs = loc->return_value();

      if(return_lhs.is_nil())
      {
        // treat these as assignments to a special symbol named 'return_value'
        auto lhs = symbol_exprt("return_value", rhs.type());
        dest << assignment_constraint(loc, std::move(lhs), std::move(rhs));
      }
      else
      {
      }
    }
  }
}

void state_encoding(
  const goto_modelt &goto_model,
  bool program_is_inlined,
  encoding_targett &dest)
{
  if(program_is_inlined)
  {
    auto f_entry = goto_model.goto_functions.function_map.find(
      goto_functionst::entry_point());

    if(f_entry == goto_model.goto_functions.function_map.end())
      throw incorrect_goto_program_exceptiont("The program has no entry point");

    dest.annotation("function " + id2string(f_entry->first));

    state_encodingt{goto_model.goto_functions}(f_entry, dest);
  }
  else
  {
    // sort alphabetically
    const auto sorted = goto_model.goto_functions.sorted();
    const namespacet ns(goto_model.symbol_table);
    for(auto &f : sorted)
    {
      const auto &symbol = ns.lookup(f->first);
      if(
        f->first == goto_functionst::entry_point() ||
        has_contract(to_code_with_contract_type(symbol.type)))
      {
        dest.annotation("");
        dest.annotation("function " + id2string(f->first));
        state_encodingt{goto_model.goto_functions}(f, dest);
      }
    }
  }
}

std::unordered_set<symbol_exprt, irep_hash>
find_variables(const std::vector<exprt> &src)
{
  std::unordered_set<symbol_exprt, irep_hash> result;

  for(auto &expr : src)
    find_variables_rec(expr, result);

  return result;
}

static typet
new_state_predicate_type(const binding_exprt::variablest &variables)
{
  mathematical_function_typet::domaint domain;
  for(auto &v : variables)
    domain.push_back(v.type());

  return mathematical_function_typet(std::move(domain), bool_typet());
}

exprt variable_encoding(exprt src, const binding_exprt::variablest &variables)
{
  // operands first
  for(auto &op : src.operands())
    op = variable_encoding(op, variables);

  if(src.id() == ID_forall)
  {
    auto &forall_expr = to_forall_expr(src);
    if(
      forall_expr.variables().size() == 1 &&
      forall_expr.symbol().type().id() == ID_state)
    {
      forall_expr
        .variables() = variables;
      return std::move(forall_expr);
    }
  }
  else if(src.id() == ID_function_application)
  {
    auto &function_application = to_function_application_expr(src);
    if(
      function_application.arguments().size() == 1 &&
      function_application.arguments().front().type().id() == ID_state)
    {
      function_application.function().type() =
        new_state_predicate_type(variables);

      if(function_application.arguments().front().id() == ID_symbol)
      {
        exprt::operandst new_arguments;
        for(auto &v : variables)
          new_arguments.push_back(v);
        function_application.arguments() = new_arguments;
      }
      else if(function_application.arguments().front().id() == ID_tuple)
      {
        DATA_INVARIANT(
          function_application.arguments().front().operands().size() ==
            variables.size(),
          "tuple size must match");
        auto operands = function_application.arguments().front().operands();
        function_application.arguments() = operands;
      }
      else
        throw analysis_exceptiont("can't convert " + format_to_string(src));
    }
    else
      throw analysis_exceptiont("can't convert " + format_to_string(src));
  }
  else if(src.id() == ID_evaluate)
  {
    auto &evaluate_expr = to_evaluate_expr(src);
    if(evaluate_expr.address().id() == ID_object_address)
      return symbol_exprt(
        to_object_address_expr(evaluate_expr.address()).object_expr());
    else
      throw analysis_exceptiont("can't convert " + format_to_string(src));
  }
  else if(src.id() == ID_update_state)
  {
    auto &update_state_expr = to_update_state_expr(src);
    if(update_state_expr.address().id() == ID_object_address)
    {
      auto lhs_symbol =
        to_object_address_expr(update_state_expr.address()).object_expr();
      exprt::operandst operands;
      for(auto &v : variables)
      {
        if(v == lhs_symbol)
          operands.push_back(update_state_expr.new_value());
        else
          operands.push_back(v);
      }
      return tuple_exprt(operands, typet(ID_state));
    }
    else
      throw analysis_exceptiont("can't convert " + format_to_string(src));
  }

  return src;
}

void variable_encoding(std::vector<exprt> &constraints)
{
  binding_exprt::variablest variables;

  for(auto &v : find_variables(constraints))
    variables.push_back(v);

  if(variables.empty())
    throw analysis_exceptiont("no variables found");

  // sort alphabetically
  std::sort(
    variables.begin(),
    variables.end(),
    [](const symbol_exprt &a, const symbol_exprt &b) {
      return id2string(a.get_identifier()) < id2string(b.get_identifier());
    });

  for(auto &c : constraints)
    c = variable_encoding(c, variables);
}

void equality_propagation(std::vector<exprt> &constraints)
{
  replace_symbolt values;

  std::vector<exprt> new_constraints;
  new_constraints.reserve(constraints.size());

  // forward-propagation of equalities
  for(auto &expr : constraints)
  {
    bool retain_constraint = true;

    // apply the map
    values(expr);

    if(expr.id() == ID_equal)
    {
      const auto &equal_expr = to_equal_expr(expr);
      if(equal_expr.lhs().id() == ID_symbol)
      {
        const auto &symbol_expr = to_symbol_expr(equal_expr.lhs());

        // this is a (deliberate) no-op when the symbol is already in the map
        if(values.replaces_symbol(symbol_expr.get_identifier()))
        {
        }
        else
        {
          values.insert(symbol_expr, equal_expr.rhs());
          // insertion has happened
          retain_constraint = false;
        }
      }
    }

    if(retain_constraint)
      new_constraints.push_back(std::move(expr));
  }

  constraints = std::move(new_constraints);

  // apply the map again, to catch any backwards definitions
  for(auto &expr : constraints)
  {
    if(expr.id() == ID_equal && to_equal_expr(expr).lhs().id() == ID_symbol)
    {
      // it's a definition
    }
    else
    {
      // apply the map
      values(expr);
    }
  }
}

void horn_encoding(const goto_modelt &goto_model, std::ostream &out)
{
  const namespacet ns(goto_model.symbol_table);

  container_encoding_targett container;
  state_encoding(goto_model, true, container);

  equality_propagation(container.constraints);

  variable_encoding(container.constraints);

  smt2_encoding_targett dest(ns, out);
  dest << container;
}
