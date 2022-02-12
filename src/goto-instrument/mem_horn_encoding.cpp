/*******************************************************************\

Module: Memory- and alias-aware basic-block-sensitive CHC encoding

Author: Grigory Fedyukovich, Saswat Padhi

\*******************************************************************/

#include "horn_encoding.h"
#include "goto_program2code.h"
#include <goto-programs/wp.h>
#include <util/find_symbols.h>
#include <util/format_expr.h>
#include <util/bitvector_types.h>

using std::set;
using std::vector;
using std::map;

// TODO: get rid of the duplicate
template <
  typename To,
  typename Container,
  typename Ti = typename Container::value_type>
std::vector<To> vector_map(const Container &input, To(*f)(const Ti &))
{
  std::vector<To> output;
  output.reserve(input.size());
  std::transform(input.begin(), input.end(), std::back_inserter(output), f);
  return output;
}

static inline bool find_alloca(exprt &expr)
{
  if (expr.id() == ID_symbol)
  {
    auto str = id2string(expr.get("identifier"));
    if (str.find("return_value_malloc") != -1)
      return true;
  }
  for (auto &a : expr.operands())
    if (find_alloca(a)) return true;
  return false;
}

static inline void find_var_symbols_arr(const exprt e,
                        set<symbol_exprt>& symbols, bool arr)
{
  find_symbols(e, symbols);
  for (auto it = symbols.begin(); it != symbols.end();)
  {
    auto ty = (*it).type().id();
    if (ty == ID_mathematical_function || ty == ID_code || ty == ID_pointer ||
        (arr && ty == ID_array))
      it = symbols.erase(it);
    else
      ++it;
  }
}

static inline void find_var_symbols(const exprt e, set<symbol_exprt>& symbols)
{
  find_var_symbols_arr(e, symbols, true);
}

unsigned int pred_num = 0;
map<exprt, exprt> cur_arrays;
vector<symbol_exprt> inv_symbs;
vector<map<exprt, exprt>> ssas;
set<symbol_exprt> cur_dep_symbols;
vector<exprt> mem;
exprt cur_app = true_exprt();
vector<exprt> nearest_loop_exit;
vector<exprt> nearest_loop_head;
vector<exprt> chcs;
int m_num = 0;
int n_num = 0;
bool use_mem = false;
bool deref_check = false;
std::string m_pref = "memor_";
std::string n_pref = "alloc_";
typet intt, arr_int_intt, arrn_int_intt;
std::ofstream enc_chc;
int qu_num = 0;
int ex_num = 0;
int de_num = 0;
bool dump_cfg;
map<exprt, exprt> prime_unprime_vars;
map<irep_idt, std::string> var_ids;

const irep_idt fun_names_to_continue[2] = {"free", "printf"};   // TODO: try
bool check_fun_name_to_continue(const irep_idt fun_name)
{
  for  (size_t i = 0; i < 2; i++)
    if (fun_names_to_continue[i] == fun_name)
      return true;
  return false;
}

std::string get_irep_id(const irep_idt n)
{
  if (var_ids[n] != "") return var_ids[n];
  auto str = std::to_string(var_ids.size());
  var_ids[n] = str;
  return str;
}

// TODO: surely, there is a better way to write this kind of things
void add_suf_expr(exprt &expr, const std::string suf)
{
  auto ty = expr.type().id();
  if(
    ty != ID_mathematical_function && ty != ID_code && ty != ID_pointer &&
    ty != ID_array && expr.id() == ID_symbol)
  {
    auto expr_copy = expr;
    expr.set("identifier", id2string(expr.get("identifier")) + "_" + suf);
    prime_unprime_vars[expr] = expr_copy;
  }
  for(auto &a : expr.operands())
    add_suf_expr(a, suf);
}

symbol_exprt unprime(symbol_exprt s)
{
  auto unpr = prime_unprime_vars[s];
  if(unpr == exprt())
    return s;
  else
    return to_symbol_expr(unpr);
}

void find_deref_selects(exprt &expr, set<exprt> &sels)
{
  if(expr.id() == ID_index)
  {
    auto str = id2string(expr.operands()[0].get("identifier"));
    if(str.find(n_pref) != -1)
    {
      sels.insert(expr);
      return;
    }
  }
  for(auto &a : expr.operands())
    find_deref_selects(a, sels);
}

void rewrite_derefs(exprt &expr)
{
  if(expr.id() == ID_if)
  {
    // getting rid of if-then-elses while accessing address_of;
    // maybe it's the source of some inaccuracy (TODO: test better)
    // but our memory model should take care of this
    auto cond = expr.operands()[0];
    if(
      cond.id() == ID_equal && cond.operands()[0].id() == ID_address_of &&
      cond.operands()[1].id() == ID_address_of)
      expr = cond.operands()[1].operands()[0];
  }
  if (expr.id() == ID_dereference && expr.get_sub().size() == 1)
  {
    auto array_offset = expr.operands()[0];
    if (array_offset.id() == ID_plus)
    {
      if (array_offset.get_sub().size() == 2)
      {
        auto array_ptr = array_offset.operands()[0];
        auto offset = array_offset.operands()[1];

        rewrite_derefs(array_ptr);
        rewrite_derefs(offset);

        index_exprt sel(
            symbol_exprt(n_pref + std::to_string(n_num), arr_int_intt),
            constant_exprt(get_irep_id(array_ptr.get("identifier")), intt));
        index_exprt sel2(
            symbol_exprt(m_pref + std::to_string(m_num), arrn_int_intt),
            sel);
        index_exprt sel3(sel2, offset);
        expr = sel3;
      }
    }
  }
  else
    for  (int i = 0; i < expr.operands().size(); i++)
      rewrite_derefs(expr.operands()[i]);
}

symbol_exprt& mk_predicate_symbol(const vector<typet> &signature)
{
  ++pred_num;
  if (use_mem)
  {
    vector<typet> mem_signature = signature;
    mem_signature.push_back(arr_int_intt);
    mem_signature.push_back(arrn_int_intt);
    inv_symbs.push_back(symbol_exprt("inv_" + std::to_string(pred_num),
      mathematical_function_typet(mem_signature, bool_typet())));
  }
  else
  {
    inv_symbs.push_back(symbol_exprt("inv_" + std::to_string(pred_num),
      mathematical_function_typet(signature, bool_typet())));
  }
  return inv_symbs.back();
}

void mk_chc(exprt src_inv, set<symbol_exprt>& src_args, exprt body_pref,
            exprt dst_inv, bool can_skip)
{
  function_application_exprt::argumentst arguments = vector_map(
    src_args, +[](const exprt &s) { return s; });

  vector<exprt> body;
  if (src_inv.type().id() == ID_mathematical_function)
  {
    if (use_mem)
    {
      arguments.push_back(
        symbol_exprt(n_pref + std::to_string(n_num), arr_int_intt));
      arguments.push_back(
        symbol_exprt(m_pref + std::to_string(m_num), arrn_int_intt));
    }
    cur_app = function_application_exprt(src_inv, arguments);
    body.push_back(cur_app);
    if (ssas.size() > 0)
      add_suf_expr(body[0].operands()[1], std::to_string(ssas.size()));
  }

  body.insert(body.end(), mem.begin(), mem.end());
  if (use_mem)
  {
    mem.clear();
    n_num = 0;
    m_num = 0;
    size_t sz = 0;
    if(dst_inv.operands().size() >= 1)
      sz = dst_inv.operands()[1].operands().size();
    if(sz >= 2)
    {
      dst_inv.operands()[1].operands()[sz - 2] =
        symbol_exprt(n_pref + std::to_string(0), arr_int_intt);
      dst_inv.operands()[1].operands()[sz - 1] =
        symbol_exprt(m_pref + std::to_string(0), arrn_int_intt);
    }
  }

  if (body_pref != true_exprt())
  {
    rewrite_derefs(body_pref);
    if (ssas.size() != 0)
      add_suf_expr(body_pref, std::to_string(ssas.size()));
    body.push_back(body_pref);
  }

  for (int i = ssas.size() - 1; i >= 0; i--) // reverse order for  convenience
  {
    for (auto & v : ssas[i])
    {
      auto src = v.first;
      if (i != 0)
        add_suf_expr(src, std::to_string(i));
      auto dst = v.second;
      add_suf_expr(dst, std::to_string(i + 1));
      body.push_back(equal_exprt(dst, src));
    }
  }

  if(
    can_skip && body.size() == 1 && dst_inv.id() == ID_function_application &&
    body[0].id() == ID_function_application &&
    body[0].operands()[1] == dst_inv.operands()[1])
  {
    // can skip
    cur_app = dst_inv;
    return;
  }

  auto body_cnjs = conjunction(body);
  chcs.push_back(implies_exprt(body_cnjs, dst_inv));

  if(deref_check)
  {
    set<exprt> sels;
    vector<exprt> eqs;
    find_deref_selects(body_cnjs, sels);
    if(!sels.empty())
    {
      for(auto &a : sels) // TODO: clean duplicates
        eqs.push_back(equal_exprt(a, constant_exprt("0", intt)));
      body.push_back(disjunction(eqs));
      chcs.push_back(implies_exprt(conjunction(body), false_exprt()));
      if(dump_cfg)
      {
        enc_chc << ' ';
        enc_chc << format(src_inv);
        enc_chc << " -> ";
        enc_chc << "deref_check_" << (de_num++);
        enc_chc << '\n';
      }
    }
  }

  if (dump_cfg)
  {
    enc_chc << ' ';
    enc_chc << format(src_inv);
    enc_chc << " -> ";
    if (dst_inv.id() == ID_function_application)
      enc_chc << format(dst_inv.operands()[0]);
    else if (dst_inv.is_true())
      enc_chc << "exit_" << (ex_num++);
    else
      enc_chc << "query_" << (qu_num++);
    enc_chc << '\n';
  }

  ssas.clear();
}

void mk_chc(exprt src_inv, set<symbol_exprt>& src_args,
            exprt dst_inv, bool can_skip)
{
  mk_chc(src_inv, src_args, true_exprt(), dst_inv, can_skip);
}

void mk_chc(exprt dst_inv, bool can_skip)
{
  set<symbol_exprt> empt;
  exprt body_pref;
  if(deref_check)
  {
    exprt ini = exprt(ID_array_of, arr_int_intt);
    ini.add_to_operands(constant_exprt("0", intt));
    body_pref = equal_exprt(
      symbol_exprt(n_pref + std::to_string(n_num), arr_int_intt), ini);
  }
  else
  {
    body_pref = true_exprt();
  }
  mk_chc(true_exprt(), empt, body_pref, dst_inv, can_skip);
}

void collect_mem(
  encoding_targett &target,
  const codet &code,
  const namespacet &ns)
{
  exprt lhs;
  exprt rhs;
  if (code.get_statement() == ID_decl)
  {
    auto cdecl = to_code_frontend_decl(code);
    if (cdecl.operands().size() == 2)
    {
      lhs = cdecl.operands()[0];
      rhs = cdecl.operands()[1];
    }
    else return;
  }
  if (code.get_statement() == ID_assign)
  {
    auto asgn = to_code_assign(code);
    lhs = asgn.lhs();
    rhs = asgn.rhs();
  }

  // TODO: extend

  if (lhs.type().id() == ID_pointer && find_alloca(rhs))
  {
    exprt eq = exprt(ID_equal);
    eq.add_to_operands(
      symbol_exprt(n_pref + std::to_string(n_num), arr_int_intt));
    n_num++;

    with_exprt str(symbol_exprt(n_pref + std::to_string(n_num), arr_int_intt),
      constant_exprt(get_irep_id(lhs.get("identifier")), intt),
      constant_exprt(get_irep_id(lhs.get("identifier")), intt));

    eq.add_to_operands(str);
    mem.push_back(eq);
  }

  if (lhs.type().id() == ID_pointer && rhs.type().id() == ID_pointer &&
      rhs.get("identifier") != "" /* TODO: better way of catching these */)
  {
    rewrite_derefs(lhs);
    rewrite_derefs(rhs);

    exprt eq = exprt(ID_equal);
    eq.add_to_operands(
      symbol_exprt(n_pref + std::to_string(n_num), arr_int_intt));

    n_num++;

    index_exprt sel(
        symbol_exprt(n_pref + std::to_string(n_num), arr_int_intt),
        constant_exprt(get_irep_id(rhs.get("identifier")), intt));

    with_exprt str(
      symbol_exprt(n_pref + std::to_string(n_num), arr_int_intt),
      constant_exprt(get_irep_id(lhs.get("identifier")), intt),
      sel);

    eq.add_to_operands(str);
    mem.push_back(eq);
    return;
  }

  if (lhs.id() == ID_dereference && lhs.get_sub().size() == 1)
  {
    const auto & array_offset = lhs.operands()[0];
    if (array_offset.id() == ID_plus)
    {
      if (array_offset.get_sub().size() == 2)
      {
        const auto & array_ptr = array_offset.operands()[0];
        auto offset = array_offset.operands()[1];

        exprt eq = exprt(ID_equal);
        eq.add_to_operands(
          symbol_exprt(m_pref + std::to_string(m_num), arrn_int_intt));

        m_num++;
        rewrite_derefs(rhs);
        rewrite_derefs(offset);
        if (ssas.size() > 0)
        {
          add_suf_expr(offset, std::to_string(ssas.size()));
          add_suf_expr(rhs, std::to_string(ssas.size()));
        }

        index_exprt sel(
            symbol_exprt(n_pref + std::to_string(n_num), arr_int_intt),
            constant_exprt(get_irep_id(array_ptr.get("identifier")), intt));
        index_exprt sel2(
            symbol_exprt(m_pref + std::to_string(m_num), arrn_int_intt), sel);

        with_exprt str(sel2, offset, rhs);
        with_exprt str2(
            symbol_exprt(m_pref + std::to_string(m_num), arrn_int_intt),
            sel, str);

        eq.add_to_operands(str2);
        mem.push_back(eq);
      }
    }
  }
}

void encode_block(
  encoding_targett &target,
  const code_blockt &block,
  const namespacet &ns,
  bool print_chcs)
{
  const auto statements = block.statements();
  for (auto it = statements.crbegin(); it != statements.crend(); ++it)
  {
    auto stmt = (*it).get_statement();
    irep_idt fun_name;
    if (stmt == ID_function_call)
      fun_name = to_code_function_call(*it).function().get("identifier");
    if (stmt == ID_ifthenelse)
    {
      // introduce a new predicate symbol
      // finalize the current chc
      exprt pre_predicate;
      if (print_chcs)
      {
        pre_predicate = mk_predicate_symbol(vector_map(
          cur_dep_symbols, +[](const symbol_exprt &s) { return s.type(); }));
        mk_chc(pre_predicate, cur_dep_symbols, cur_app, false);
      }

      // start new blocks
      auto ite = to_code_ifthenelse(*it);
      code_blockt then_block, else_block;
      if (ite.then_case().get_statement() == ID_block)
        then_block = to_code_block(ite.then_case());
      else
        then_block.add(ite.then_case());

      if (ite.else_case().get_statement() == ID_block)
        else_block = to_code_block(ite.else_case());
      else if (ite.else_case().get_statement() != "")  // for  empty else-branch
        else_block.add(ite.else_case());

      auto cur_args = cur_app.operands()[1];
      auto cur_app2 = cur_app;
      encode_block(target, then_block, ns, print_chcs);   // rec.call
      auto arg_symbols_tmp = cur_dep_symbols;

      find_var_symbols(ite.cond(), cur_dep_symbols);
      auto new_predicate = mk_predicate_symbol(vector_map(
        cur_dep_symbols, +[](const symbol_exprt &s) { return s.type(); }));

      if (print_chcs)
        mk_chc(new_predicate, cur_dep_symbols, ite.cond(), cur_app, false);
      auto cur_app3 = cur_app;

      cur_app = cur_app2;
      encode_block(target, else_block, ns, print_chcs);

      if (print_chcs)
      {
        if (cur_dep_symbols == arg_symbols_tmp)
        {
          mk_chc(new_predicate, cur_dep_symbols,
            not_exprt(ite.cond()), cur_app, false);
        }
        else
        {
          auto new_predicate2 = mk_predicate_symbol(vector_map(
              cur_dep_symbols, +[](const symbol_exprt &s) { return s.type(); }));

          mk_chc(new_predicate2, cur_dep_symbols,
            not_exprt(ite.cond()), cur_app, false);
          mk_chc(new_predicate2, cur_dep_symbols,
            cur_app3, false);
        }
      }
    }
    else if (stmt == ID_assert ||
             stmt == ID_assume ||
            (stmt == ID_function_call && fun_name == "assume"))
    {
      // similar to if -then-else, except that the "then"-branch immediately goes away
      exprt pre_predicate;
      if (print_chcs)
      {
        pre_predicate = mk_predicate_symbol(vector_map(
          cur_dep_symbols, +[](const symbol_exprt &s) { return s.type(); }));
        mk_chc(pre_predicate, cur_dep_symbols, cur_app, false);
      }

      exprt assm;
      if (stmt == ID_assert)
        assm = to_code_assert(*it).assertion();
      else if (stmt == ID_assume)
        assm = to_code_assume(*it).assumption();
      else
        assm = to_code_function_call(*it).arguments()[0];
      find_var_symbols(assm, cur_dep_symbols);

      if (print_chcs)
      {
        auto new_predicate = mk_predicate_symbol(vector_map(
          cur_dep_symbols, +[](const symbol_exprt &s) { return s.type(); }));
              // successful assertions are treated as assumptions
        mk_chc(new_predicate, cur_dep_symbols, assm, cur_app, false);
              // unsuccessful assumptions (resp. assertions) are ignored (resp. punished)
        mk_chc(new_predicate, cur_dep_symbols, not_exprt(assm),
                (stmt == ID_assert ? (exprt)false_exprt() :
                                     (exprt)true_exprt()), false);
      }
    }
    else if (stmt == ID_for || stmt == ID_while || stmt == ID_dowhile)
    {
      exprt cond;
      code_blockt body_block;
      if (stmt == ID_for)
      {
        auto cfor = to_code_for(*it);
        if (cfor.body().get_statement() == ID_block)
          body_block = to_code_block(cfor.body());
        else
          body_block.add(cfor.body());
        auto iter = to_side_effect_expr_assign(cfor.iter());
        body_block.add(code_assignt(iter.lhs(), iter.rhs()));
        cond = cfor.cond();
      }
      else if (stmt == ID_while)
      {
        auto cwhile = to_code_while(*it);
        if (cwhile.body().get_statement() == ID_block)
          body_block = to_code_block(cwhile.body());
        else
          body_block.add(cwhile.body());
        cond = cwhile.cond();
      }
      else
      {
        auto cdwhile = to_code_dowhile(*it);
        if (cdwhile.body().get_statement() == ID_block)
          body_block = to_code_block(cdwhile.body());
        else
          body_block.add(cdwhile.body());
        cond = cdwhile.cond();
      }

      find_var_symbols(cond, cur_dep_symbols);
      exprt pre_predicate;
      if (print_chcs)                    // loop termination
      {
        nearest_loop_exit.push_back(cur_app);
        pre_predicate = mk_predicate_symbol(vector_map(
          cur_dep_symbols, +[](const symbol_exprt &s) { return s.type(); }));
        mk_chc(pre_predicate, cur_dep_symbols, not_exprt(cond), cur_app, false);
      }

      while(true)                     // iteratively finding dependend variables
      {
        auto cur_dep_symbols_tmp = cur_dep_symbols;
        encode_block(target, body_block, ns, false);     // rec.call

        if (cur_dep_symbols != cur_dep_symbols_tmp)
        {
          ssas.clear();
          pre_predicate = mk_predicate_symbol(vector_map(
            cur_dep_symbols, +[](const symbol_exprt &s) { return s.type(); }));
          mk_chc(pre_predicate, cur_dep_symbols, cur_app, false);
        }
        else
        {
          if (print_chcs)
          {
            ssas.clear();
            nearest_loop_head.push_back(cur_app);
            encode_block(target, body_block, ns, true);  // rec.call

            // if `do-while`, the incoming and outgoing rules
            // should use different predicates. otherwise, the same
            exprt tmp;
            if (stmt == ID_dowhile) tmp = cur_app;
            mk_chc(pre_predicate, cur_dep_symbols, cond, cur_app, false);
            if (stmt == ID_dowhile) cur_app = tmp;
            nearest_loop_exit.pop_back();
            nearest_loop_head.pop_back();
          }
          break;
        }
      }
    }
    else if (stmt == ID_assign || stmt == ID_decl)
    {
      if(use_mem)
        collect_mem(target, *it, ns);

      set<symbol_exprt> dep_symbols_pre;
      map<exprt, exprt> next_vars;
      codet cod(stmt);
      if (stmt == ID_assign)
      {
        cod = to_code_assign(*it);
        if (cod.op1().id() == ID_side_effect)
          continue;  // TODO: maybe support better
      }
      else
      {
        auto cdecl = to_code_frontend_decl(*it);
        if (cdecl.operands().size() < 2)
          cod = cdecl;
        else
        {
          if (cdecl.op1().id() == ID_side_effect)
            continue;  // TODO: maybe support better
          cod = code_assignt(cdecl.op0(), cdecl.op1());
        }
      }

      for (auto & s : cur_dep_symbols)
      {
        auto wp_sym = wp(cod, s, ns);
        if (wp_sym.get("statement") == ID_nondet)
          wp_sym = s;     // to optimize
        if(use_mem)
          rewrite_derefs(wp_sym);
        next_vars[s] = wp_sym;
        find_var_symbols(wp_sym, dep_symbols_pre);
      }
      if(!next_vars.empty())
      {
        bool all_eq = true; // small optim
        for(auto &v : next_vars)
          if(v.first != v.second)
            all_eq = false;
        if(!all_eq)
          ssas.push_back(next_vars);
        cur_dep_symbols.insert(dep_symbols_pre.begin(), dep_symbols_pre.end());
      }
      if(use_mem)
      {
        set<symbol_exprt> primed_symbols;
        for(auto &m : mem)
          find_var_symbols(m, primed_symbols);

        for(auto &s : primed_symbols)
        {
          auto a = unprime(s);
          cur_dep_symbols.insert(a);
        }

        if(!print_chcs)
        {
          mem.clear();
          n_num = 0;
          m_num = 0;
        }
      }
    }
    else if (stmt == ID_block)
    {
      encode_block(target, to_code_block(*it), ns, true);
    }
    else if (stmt == ID_break || stmt == ID_continue)
    {
      if (print_chcs)
      {
        cur_app = stmt == ID_break ?
          nearest_loop_exit.back() : nearest_loop_head.back();
        ssas.clear();
        if (use_mem)
        {
          mem.clear();
          n_num = 0;
          m_num = 0;
        }
      }
    }
    else if (stmt == ID_output || stmt == ID_label || stmt == ID_skip ||
            (stmt == ID_function_call && check_fun_name_to_continue(fun_name)))
    {
      continue;
    }
    else
    {
      assert(0 && "unsupported");
    }
  }
  if (print_chcs)
  {
    if (!cur_dep_symbols.empty())
    {
      auto fin_predicate = mk_predicate_symbol(vector_map(
        cur_dep_symbols, +[](const symbol_exprt &s) { return s.type(); }));
      mk_chc(fin_predicate, cur_dep_symbols, cur_app, true);
    }
  }
}

void output_result(encoding_targett &target)
{
  for (auto c = chcs.rbegin(); c != chcs.rend(); ++c)
  {
    auto &constraint = *c;
    set<symbol_exprt> local_signature;
    find_var_symbols_arr(constraint, local_signature, false);
    if (local_signature.empty())
      target.output_exprt(constraint);
    else
      target.output_exprt(forall_exprt(vector_map(
        local_signature, +[](const symbol_exprt &s) { return s; }), constraint));
  }
}


std::function<void(encoding_targett &)> mem_encode_function(
  irep_idt identifier,
  const goto_functiont &function,
  const symbol_tablet &symbol_table)
{
  return [&](encoding_targett &target) {
    if (!function.body.empty())
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

      // init the dot-file for  debugging
      if (dump_cfg)
      {
        enc_chc.open("chc.dot");
        enc_chc <<("digraph print {\n");
      }

      // init types used in for  memory model
      intt = integer_bitvector_typet(ID_signedbv, 64);
      arr_int_intt = array_typet(intt, symbol_exprt("tmp", intt));
      arrn_int_intt = array_typet(arr_int_intt, symbol_exprt("tmp", intt));

      // fun the actual encoding
      encode_block(target, block, ns, true);
      mk_chc(cur_app, false);  // fact

      // finalizing the degug file
      if (dump_cfg)
      {
        enc_chc << "}";
        enc_chc.close();
        // this needs a graphiz package installed:
        system("dot -Tpdf -o chc.pdf chc.dot");
      }

      for (auto v : var_ids)
        target.output("; var_id: " + id2string(v.first) +
                     "; " + v.second + "\n");

      // print to CHC file
      output_result(target);
    }
    else
      DATA_INVARIANT(false, "Cannot encode an empty function!");
  };
}

void horn_encoding(
  const goto_modelt &model,
  std::ostream &out,
  bool _use_mem,
  bool _deref_check,
  bool _dump_cfg)
{
  use_mem = _use_mem;
  deref_check = _use_mem && _deref_check;
  dump_cfg = _dump_cfg;
  std::ofstream enc;
  enc.open("enc.smt2");
  const auto &functions = model.get_goto_functions();
  const auto &entry_point =
    functions.function_map.find(functions.entry_point());
  const namespacet ns(model.symbol_table);
  smt2_encoding_targett target(enc, ns);
  target << mem_encode_function(
    entry_point->first, entry_point->second, model.symbol_table);
  target.output("\n(check-sat)");
  out << "Encoded to `enc.smt2`\n";
  // TODO: use the solver further
}
