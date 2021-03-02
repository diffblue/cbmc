/*******************************************************************\

Module: Horn-clause Encoding

Author: Saswat Padhi

\*******************************************************************/

/// \file
/// Horn-clause Encoding

#include "horn_encoding.h"
#include "goto_program2code.h"

#include <analyses/natural_loops.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/wp.h>

#include <util/find_symbols.h>
#include <util/format_expr.h>
#include <util/mathematical_types.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <functional>
#include <iostream>
#include <ostream>
#include <set>
#include <tuple>
#include <vector>

using std::set;
using std::stack;
using std::tuple;
using std::vector;

const true_exprt DEFAULT_POSTCONDITION;

template <
  typename To,
  typename Container,
  typename Ti = typename Container::value_type>
std::vector<To> vector_map(const Container &input, To (*f)(const Ti &))
{
  std::vector<To> output;
  output.reserve(input.size());
  std::transform(input.begin(), input.end(), std::back_inserter(output), f);
  return output;
}

static unsigned int loop_number = 0;
symbol_exprt make_invariant_symbol(const vector<typet> &signature)
{
  ++loop_number;
  return symbol_exprt(
    "loop_invariant_" + std::to_string(loop_number),
    mathematical_function_typet(signature, bool_typet()));
}

struct wp_result
{
  exprt pre;
  vector<exprt> extra_constraints;
  vector<symbol_exprt> extra_invariants;
};

void merge_result_extras(wp_result &src, wp_result &dst)
{
  std::move(
    src.extra_invariants.begin(),
    src.extra_invariants.end(),
    std::back_inserter(dst.extra_invariants));
  std::move(
    src.extra_constraints.begin(),
    src.extra_constraints.end(),
    std::back_inserter(dst.extra_constraints));
}

wp_result compute_wp(
  encoding_targett &target,
  const codet &code,
  const exprt &post,
  const namespacet &ns);

wp_result compute_wp_assert(
  encoding_targett &target,
  const code_assertt &cassert,
  const exprt &post,
  const namespacet &ns)
{
  target.comment_stream() << "  [ASSERT]: " << format(cassert) << "\n";
  target.comment_stream() << "      POST: " << format(post) << "\n";

  wp_result result{simplify_expr(and_exprt(cassert.assertion(), post), ns)};

  target.comment_stream() << "WP[ASSERT]: " << format(result.pre) << "\n\n";
  return result;
}

wp_result compute_wp_ifthenelse(
  encoding_targett &target,
  const code_ifthenelset &ite,
  const exprt &post,
  const namespacet &ns)
{
  target.comment_stream() << "   [I_T_E]: " << format(ite) << "\n";
  target.comment_stream() << "      POST: " << format(post) << "\n";

  wp_result wp_then{DEFAULT_POSTCONDITION};
  if(ite.then_case().is_not_nil())
    wp_then = compute_wp(target, ite.then_case(), post, ns);

  wp_result wp_else{DEFAULT_POSTCONDITION};
  if(ite.else_case().is_not_nil())
    wp_else = compute_wp(target, ite.else_case(), post, ns);

  wp_result result;
  result.pre = simplify_expr(
    and_exprt(
      implies_exprt(ite.cond(), wp_then.pre),
      implies_exprt(not_exprt(ite.cond()), wp_else.pre)),
    ns);

  merge_result_extras(wp_then, result);
  merge_result_extras(wp_else, result);

  target.comment_stream() << " WP[I_T_E]: " << format(result.pre) << "\n\n";
  return result;
}

wp_result compute_wp_block(
  encoding_targett &target,
  const code_blockt &block,
  const exprt &post,
  const namespacet &ns)
{
  target.comment_stream() << "   [BLOCK]: " << format(block) << "\n";
  target.comment_stream() << "      POST: " << format(post) << "\n";

  wp_result result;
  exprt current_post = post;
  const auto statements = block.statements();
  for(auto it = statements.crbegin(); it != statements.crend(); ++it)
  {
    auto wp_it = compute_wp(target, *it, current_post, ns);
    merge_result_extras(wp_it, result);
    current_post = wp_it.pre;
  }
  result.pre = current_post;

  target.comment_stream() << " WP[BLOCK]: " << format(result.pre) << "\n\n";
  return result;
}

wp_result compute_wp_while(
  encoding_targett &target,
  const code_whilet &cwhile,
  const exprt &post,
  const namespacet &ns)
{
  target.comment_stream() << "   [WHILE]: " << format(cwhile) << "\n";
  target.comment_stream() << "      POST: " << format(post) << "\n";

  set<symbol_exprt> local_symbols;
  find_symbols(post, local_symbols);
  find_symbols(cwhile.cond(), local_symbols);
  find_symbols(cwhile.body(), local_symbols);

  vector<symbol_exprt> local_signature;
  for(const auto &s : local_symbols)
    if(s.type().id() != ID_mathematical_function)
      local_signature.push_back(s);

  function_application_exprt::argumentst arguments = vector_map(
    local_signature, +[](const exprt &s) { return s; });

  wp_result result;
  auto new_invariant = make_invariant_symbol(vector_map(
    local_signature, +[](const symbol_exprt &s) { return s.type(); }));
  result.pre = function_application_exprt(new_invariant, arguments);
  auto wp_body = compute_wp(target, cwhile.body(), result.pre, ns);

  merge_result_extras(wp_body, result);

  result.extra_constraints.push_back(
    implies_exprt(and_exprt(cwhile.cond(), result.pre), wp_body.pre));
  result.extra_constraints.push_back(
    implies_exprt(and_exprt(not_exprt(cwhile.cond()), result.pre), post));

  result.extra_invariants.push_back(new_invariant);

  target.comment_stream() << " WP[WHILE]: " << format(result.pre) << "\n\n";
  return result;
}

wp_result compute_wp_decl(
  encoding_targett &target,
  const code_declt &cdecl,
  const exprt &post,
  const namespacet &ns)
{
  if(cdecl.operands().size() < 2)
    return wp_result{post};
  else
    return compute_wp(target, code_assignt(cdecl.op0(), cdecl.op1()), post, ns);
}

wp_result compute_wp_for(
  encoding_targett &target,
  const code_fort &cfor,
  const exprt &post,
  const namespacet &ns)
{
  code_blockt body;
  if(cfor.body().get_statement() == ID_block)
    body = to_code_block(cfor.body());
  else
    body.add(cfor.body());

  // TODO: Check with DiffBlue:
  // How does a `code_assignt` differ from a `side_effect_expr_assignt`??
  auto iter = to_side_effect_expr_assign(cfor.iter());
  body.add(code_assignt(iter.lhs(), iter.rhs()));
  code_whilet cwhile(cfor.cond(), body);

  return compute_wp_while(target, cwhile, post, ns);
}

wp_result compute_wp(
  encoding_targett &target,
  const codet &code,
  const exprt &post,
  const namespacet &ns)
{
  const irep_idt &statement = code.get_statement();
  if(statement == ID_assert)
    return compute_wp_assert(target, to_code_assert(code), post, ns);
  else if(statement == ID_ifthenelse)
    return compute_wp_ifthenelse(target, to_code_ifthenelse(code), post, ns);
  else if(statement == ID_while)
    return compute_wp_while(target, to_code_while(code), post, ns);
  else if(statement == ID_for)
    return compute_wp_for(target, to_code_for(code), post, ns);
  else if(statement == ID_decl)
    return compute_wp_decl(target, to_code_decl(code), post, ns);
  else if(statement == ID_block)
    return compute_wp_block(target, to_code_block(code), post, ns);
  else if(statement == ID_label)
    return wp_result{post};
  else
  {
    target.comment_stream()
      << "   [" << id2string(statement) << "]: " << format(code) << "\n";
    target.comment_stream() << "      POST: " << format(post) << "\n";

    // TODO: Why does `simplify_expr` cause an invariant violation below?
    wp_result result{wp(code, post, ns)};

    target.comment_stream() << " WP[" << id2string(statement)
                            << "]: " << format(result.pre) << "\n\n";
    return result;
  }
}

void output_result(encoding_targett &target, wp_result result)
{
  target.comment_break('-');
  unsigned k = 1;
  target.comment_stream() << "\nFinal constraints:\n";
  for(const auto &constraint : result.extra_constraints)
  {
    target.comment_stream()
      << "\n   " << k++ << ". " << format(constraint) << "\n";

    set<symbol_exprt> local_symbols;
    find_symbols(constraint, local_symbols);
    vector<symbol_exprt> local_signature;
    for(const auto &s : local_symbols)
      if(s.type().id() != ID_mathematical_function)
        local_signature.push_back(s);

    target.output_exprt(forall_exprt(local_signature, constraint));
  }
  target.comment_stream() << "\n";

  target.comment_break('-');
  target.comment_stream() << "\nRequired invariants:\n";
  k = 1;
  for(const auto &inv : result.extra_invariants)
    target.comment_stream() << "   " << k++ << ". " << format(inv) << "\n";

  target.comment_stream() << "\n";
  target.comment_break('=');
}

// void cleanup_loops(
//   code_blockt &block,
//   const namespacet &ns)
// {
//   auto &statements = block.statements();
//   for(size_t i = 0; i < statements.size(); i++)
//   {
//     if(statements[i].get_statement() == ID_dowhile)
//     {
//       auto &cdowhile = to_code_dowhile(statements[i]);
//       auto cond = simplify_expr(cdowhile.cond(), ns);
//       auto &body = cdowhile.body();

//       if(cond.id() != ID_constant) continue;
//       auto ccond = to_constant_expr(cond);
//       if(ccond.get_value() != ID_false) continue;

//       if(body.get_statement() == ID_block)
//         cleanup_loops(to_code_block(body), ns);
//       statements[i] = body;
//     }
//   }
// }

std::function<void(encoding_targett &)> encode_function(
  irep_idt identifier,
  const goto_functiont &function,
  const symbol_tablet &symbol_table)
{
  return [&](encoding_targett &target) {
    if(!function.body.empty())
    {
      namespacet ns(symbol_table);

      code_blockt block;
      symbol_tablet st_copy(symbol_table);
      std::list<irep_idt> local_static, type_names;
      std::unordered_set<irep_idt> typedef_names;
      std::set<std::string> system_headers;
      goto_program2codet codify(
        identifier,
        function.body,
        st_copy,
        block,
        local_static,
        type_names,
        typedef_names,
        system_headers);
      codify();

      target.comment_break('=');
      target.comment_stream() << "\n";

      auto result = compute_wp(target, block, DEFAULT_POSTCONDITION, ns);
      result.extra_constraints.push_back(result.pre);
      output_result(target, result);
    }
    else
      DATA_INVARIANT(false, "Cannot encode an empty function!");
  };
}

void horn_encoding(
  const goto_modelt &model,
  horn_formatt format,
  std::ostream &out)
{
  const auto &functions = model.get_goto_functions();
  const auto &entry_point =
    functions.function_map.find(functions.entry_point());

  switch(format)
  {
  case horn_formatt::ASCII:
  {
    text_encoding_targett target(out);
    target << encode_function(
      entry_point->first, entry_point->second, model.symbol_table);
  }
  break;

  case horn_formatt::SMT2:
  {
    const namespacet ns(model.symbol_table);
    smt2_encoding_targett target(out, ns);
    target << encode_function(
      entry_point->first, entry_point->second, model.symbol_table);
    target.output("\n(check-sat)\n(get-model)");
  }
  break;
  }
}
