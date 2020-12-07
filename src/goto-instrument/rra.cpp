/*******************************************************************\

Module: Replication Reducing Abstraction

Author: Adrian Palacios accorell@amazon.com
        Murali Talupur  talupur@amazon.com
        Lefan Zhang     lefanz@amazon.com

\*******************************************************************/

/// \file
/// Replication Reducing Abstraction
/// Abstract certain data types to make proofs unbounded

#include <iostream>
#include <queue>

#include "rra.h"

#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_goto_model.h>
#include <linking/static_lifetime_init.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/std_expr.h>
#include <util/pointer_expr.h>

rrat::expr_type_relationt::expr_type_relationt(const rra_spect::spect &spec)
{
  for(const auto &array_p : spec.get_abst_arrays())
    seeds.insert({array_p.first, rra_spect::spect::entityt::ARRAY});
  for(const auto &array_p : spec.get_abst_const_c_strs())
    seeds.insert({array_p.first, rra_spect::spect::entityt::CONST_C_STR});
  for(const auto &index_p : spec.get_abst_indices())
    seeds.insert({index_p.first, rra_spect::spect::entityt::SCALAR});
}

void rrat::expr_type_relationt::link_exprt_equiv(size_t i1, size_t i2)
{
  edges_equiv[i1].insert(i2);
  edges_equiv[i2].insert(i1);

  if(is_entity_expr(expr_list[i1]) && is_entity_expr(expr_list[i2]))
  {
    const irep_idt str_id1 = get_string_id_from_exprt(expr_list[i1]);
    const irep_idt str_id2 = get_string_id_from_exprt(expr_list[i2]);
    link_entity_equiv(str_id1, str_id2);
  }
  else if(
    is_entity_expr(expr_list[i1]) && expr_list[i2].id() == ID_address_of &&
    is_entity_expr(expr_list[i2].operands()[0]))
  {
    const irep_idt str_id1 = get_string_id_from_exprt(expr_list[i1]);
    const irep_idt str_id2 =
      get_string_id_from_exprt(expr_list[i2].operands()[0]);
    link_entity_addr_of(str_id1, str_id2);
  }
  else if(
    is_entity_expr(expr_list[i2]) && expr_list[i1].id() == ID_address_of &&
    is_entity_expr(expr_list[i1].operands()[0]))
  {
    const irep_idt str_id2 = get_string_id_from_exprt(expr_list[i2]);
    const irep_idt str_id1 =
      get_string_id_from_exprt(expr_list[i1].operands()[0]);
    link_entity_addr_of(str_id2, str_id1);
  }
  else
  {
  }
}

void rrat::expr_type_relationt::link_exprt_access(size_t i1, size_t i2)
{
  edges_access[i1].insert(i2);
}

void rrat::expr_type_relationt::link_entity_equiv(
  irep_idt symb1,
  irep_idt symb2)
{
  entity_edges_equiv[symb1].insert(symb2);
  entity_edges_equiv[symb2].insert(symb1);
}

void rrat::expr_type_relationt::link_entity_addr_of(
  irep_idt symb1,
  irep_idt symb2)
{
  entity_edges_addr_of[symb1].insert(symb2);
}

size_t rrat::expr_type_relationt::add_expr(const exprt &expr)
{
  size_t index = expr_list.size();
  expr_list.push_back(expr);
  edges_equiv.push_back(std::unordered_set<size_t>());
  edges_access.push_back(std::unordered_set<size_t>());

  // add symbol to symbol list
  if(is_entity_expr(expr))
  {
    const irep_idt str_id = get_string_id_from_exprt(expr);
    if(symbols.find(str_id) == symbols.end())
      symbols[str_id] = std::unordered_set<size_t>();
    if(entity_edges_equiv.find(str_id) == entity_edges_equiv.end())
      entity_edges_equiv[str_id] = std::unordered_set<irep_idt>();
    if(entity_edges_addr_of.find(str_id) == entity_edges_addr_of.end())
      entity_edges_addr_of[str_id] = std::unordered_set<irep_idt>();
    // if this exprt is an entity, store this information
    symbols[str_id].insert(index);
    // if the symbol is one of the seeds, put it into the todo list
    if(seeds.find(str_id) != seeds.end())
      todo.insert({index, seeds[str_id]});
  }

  // add operands also
  if(expr.has_operands())
  {
    std::vector<size_t> operands_index;
    for(auto &op : expr.operands())
      operands_index.push_back(add_expr(op));

    if(
      expr.id() == ID_equal || expr.id() == ID_notequal || expr.id() == ID_ge ||
      expr.id() == ID_gt || expr.id() == ID_le || expr.id() == ID_lt)
    {
      link_exprt_equiv(operands_index[0], operands_index[1]);
    }
    else if(
      expr.id() == ID_const_cast || expr.id() == ID_static_cast ||
      expr.id() == ID_typecast || expr.id() == ID_dynamic_cast ||
      expr.id() == ID_reinterpret_cast)
    {
      link_exprt_equiv(index, operands_index[0]);
    }
    else if(expr.id() == ID_plus || expr.id() == ID_minus)
    {
      if(
        expr.operands()[0].id() == ID_symbol ||
        expr.operands()[0].id() == ID_member)
      {
        if(
          (expr.operands()[1].id() == ID_typecast &&
           expr.operands()[1].operands()[0].id() == ID_constant) ||
          expr.operands()[1].id() == ID_constant)
        {
          link_exprt_equiv(index, operands_index[0]);
        }
      }
    }

    // If this is an access to the array, insert that edge
    if(
      expr.id() == ID_plus && (is_entity_expr(expr.operands().front())) &&
      expr.operands().front().type().id() == ID_pointer)
    {
      link_exprt_access(operands_index[0], operands_index[1]);
    }
  }

  return index;
}

int rrat::expr_type_relationt::check_symb_deref_level(
  irep_idt symb1,
  irep_idt symb2)
{
  std::unordered_map<irep_idt, int> finished;
  std::queue<irep_idt> todo;

  // the starting node should be 0 level
  todo.push(symb1);
  finished.insert({symb1, 0});

  while(!todo.empty())
  {
    irep_idt current_symb = todo.front();
    INVARIANT(
      symbols.find(current_symb) != symbols.end(),
      "the symbol " + std::string(current_symb.c_str()) +
        " should be in the symbol list.");
    INVARIANT(
      entity_edges_equiv.find(current_symb) != entity_edges_equiv.end(),
      "the symbol " + std::string(current_symb.c_str()) +
        " should be in the symbol list.");
    INVARIANT(
      entity_edges_addr_of.find(current_symb) != entity_edges_addr_of.end(),
      "the symbol " + std::string(current_symb.c_str()) +
        " should be in the symbol list.");
    todo.pop();

    for(const auto &eq_ngbr : entity_edges_equiv[current_symb])
    {
      if(finished.find(eq_ngbr) == finished.end())
      {
        todo.push(eq_ngbr);
        finished.insert({eq_ngbr, finished[current_symb]});
      }
      else
      {
        INVARIANT(
          finished[eq_ngbr] == finished[current_symb],
          "the reference level between " + std::string(current_symb.c_str()) +
            " and " + std::string(eq_ngbr.c_str()) + " are not consistent");
      }
    }

    for(const auto &addr_ngbr : entity_edges_addr_of[current_symb])
    {
      if(finished.find(addr_ngbr) == finished.end())
      {
        todo.push(addr_ngbr);
        finished.insert({addr_ngbr, finished[current_symb] + 1});
      }
      else
      {
        INVARIANT(
          finished[addr_ngbr] == finished[current_symb] + 1,
          "the reference level between " + std::string(current_symb.c_str()) +
            " and " + std::string(addr_ngbr.c_str()) + " are not consistent");
      }
    }
  }

  if(finished.find(symb2) != finished.end())
    return finished[symb2];
  else
    return -1;
}

bool rrat::expr_type_relationt::is_equiv_entity(irep_idt symb1, irep_idt symb2)
{
  INVARIANT(
    symbols.find(symb1) != symbols.end(),
    "Symbol " + std::string(symb1.c_str()) + " is not found");
  INVARIANT(
    entity_edges_equiv.find(symb1) != entity_edges_equiv.end(),
    "Symbol " + std::string(symb1.c_str()) + " is not found");
  INVARIANT(
    entity_edges_addr_of.find(symb1) != entity_edges_addr_of.end(),
    "Symbol " + std::string(symb1.c_str()) + " is not found");
  INVARIANT(
    symbols.find(symb2) != symbols.end(),
    "Symbol " + std::string(symb2.c_str()) + " is not found");
  INVARIANT(
    entity_edges_equiv.find(symb2) != entity_edges_equiv.end(),
    "Symbol " + std::string(symb2.c_str()) + " is not found");
  INVARIANT(
    entity_edges_addr_of.find(symb2) != entity_edges_addr_of.end(),
    "Symbol " + std::string(symb2.c_str()) + " is not found");

  // are they just the same?
  if(symb1 == symb2)
    return true;
  // do they have a direct equivalence?
  if(check_symb_deref_level(symb1, symb2) == 0)
    return true;
  // are they equivalent because of the equiv of their parent?
  auto parent_p1 = get_parent_id(symb1);
  auto parent_p2 = get_parent_id(symb2);
  if(parent_p1.first != "" && parent_p2.first != "")
  {
    // e.g. a.len => (flag: ".", parent: "a", child: "len")
    std::string flag1 = parent_p1.first;
    std::string parent1 = parent_p1.second.c_str();
    std::string child1 =
      std::string(symb1.c_str()).substr(parent1.size() + flag1.size());
    std::string flag2 = parent_p2.first;
    std::string parent2 = parent_p2.second.c_str();
    std::string child2 =
      std::string(symb2.c_str()).substr(parent2.size() + flag2.size());
    if(child1 != child2)
    {
      return false;
    }
    else
    {
      if(flag1 == flag2)
      {
        return check_symb_deref_level(irep_idt(parent1), irep_idt(parent2)) ==
               0;
      }
      else
      {
        irep_idt p1_idt = parent1;
        irep_idt p2_idt = parent2;
        // is a->len and b.len equivalent? it depends on whether a = &b
        if(flag1 == "->" && flag2 == ".")
          return check_symb_deref_level(p1_idt, p2_idt) == 1;
        else if(flag1 == "." && flag2 == "->")
          return check_symb_deref_level(p2_idt, p1_idt) == 1;
        else
          throw "flag should be either -> or .";
      }
    }
  }
  else
  {
    return false;
  }
}

std::vector<std::pair<size_t, rra_spect::spect::entityt::entityt_type>>
rrat::expr_type_relationt::get_neighbors(
  size_t index,
  rra_spect::spect::entityt::entityt_type type)
{
  // step 1: get all neighbors related with direct edges
  std::vector<std::pair<size_t, rra_spect::spect::entityt::entityt_type>>
    results;
  if(
    type == rra_spect::spect::entityt::ARRAY ||
    type == rra_spect::spect::entityt::CONST_C_STR)
  {
    // edge neighbors should consist of edge_equiv and edge_index
    for(const size_t &ngbr_id : edges_equiv[index])
      results.push_back(std::make_pair(ngbr_id, type));
    for(const size_t &ngbr_id : edges_access[index])
      results.push_back(
        std::make_pair(ngbr_id, rra_spect::spect::entityt::SCALAR));
  }
  else if(
    type == rra_spect::spect::entityt::SCALAR ||
    type == rra_spect::spect::entityt::LENGTH)
  {
    // edge neighbors should consist of edge_equiv only
    for(const size_t &ngbr_id : edges_equiv[index])
      results.push_back(
        std::make_pair(ngbr_id, rra_spect::spect::entityt::SCALAR));
  }
  else
  {
    const char *seed_error =
      "seeds of type other than ARRAY, CONST_C_STR, "
      "SCALAR and LENGTH shouldn't appear in closure analysis. Type val: ";
    throw seed_error + std::to_string(type);
  }

  // step 2: get the equiv neighbors because of using the same symbol
  if(is_entity_expr(expr_list[index]))
  {
    irep_idt symb_name = get_string_id_from_exprt(expr_list[index]);
    // step 2.1: put all exprs using the same symbol as neighbors
    // e.g. the same symbol is referenced in different places as exprs.
    // Those exprs should be neighbors
    for(const size_t &ngbr_id : symbols[symb_name])
      if(ngbr_id != index)
        results.push_back(std::make_pair(ngbr_id, type));

    // step 2.2: put all exprs refering to the same struct member as neighbors
    // e.g. a = &b; then a->len and b.len should refer to the same symbol,
    // and thus be neighbors
    for(const auto &symb_p : symbols)
    {
      const irep_idt &ngbr_symb_name = symb_p.first;
      if(
        ngbr_symb_name != symb_name &&
        is_equiv_entity(ngbr_symb_name, symb_name))
      {
        for(const size_t &ngbr_id : symbols[ngbr_symb_name])
          results.push_back(std::make_pair(ngbr_id, type));
      }
    }
  }

  return results;
}

void rrat::expr_type_relationt::solve()
{
  while(!todo.empty())
  {
    auto current_it = todo.begin();
    size_t current_index = current_it->first;
    auto current_type = current_it->second;

    // step 1: insert this into finished and remove it from the todo
    INVARIANT(
      finished.find(current_index) == finished.end(),
      "an exprt node is analyzed twice in closure analysis");
    finished.insert({current_index, current_type});
    todo.erase(current_index);

    // step 2: if this is a symbol, store it into the newly found entity list
    if(is_entity_expr(expr_list[current_index]))
    {
      const irep_idt str_id =
        get_string_id_from_exprt(expr_list[current_index]);
      if(
        seeds.find(str_id) == seeds.end() &&
        new_entities.find(str_id) == new_entities.end())
        new_entities.insert({str_id, current_type});
    }

    // step 3: visit all neighbors, put them into the todo list if needed
    std::vector<std::pair<size_t, rra_spect::spect::entityt::entityt_type>>
      neighbors = get_neighbors(current_index, current_type);
    for(const auto &ngbr : neighbors)
      if(
        todo.find(ngbr.first) == todo.end() &&
        finished.find(ngbr.first) == finished.end())
        todo.insert(ngbr);
  }
}

std::unordered_map<irep_idt, rra_spect::spect::entityt::entityt_type>
rrat::expr_type_relationt::get_new_entities()
{
  return new_entities;
}

irep_idt rrat::get_string_id_from_exprt(const exprt &expr)
{
  if(expr.id() == ID_symbol)
  {
    const symbol_exprt &symb_expr = to_symbol_expr(expr);
    return symb_expr.get_identifier();
  }
  else if(expr.id() == ID_member)
  {
    INVARIANT(
      expr.operands().size() == 1,
      "member access should only have one operand");
    const member_exprt &mem_expr = to_member_expr(expr);
    const exprt &obj_expr = expr.operands()[0];
    const irep_idt &comp_name = mem_expr.get_component_name();

    // we need to get rid of dereference/address_of pairs
    // e.g. *&*&buf
    exprt current_obj_expr = obj_expr;
    while((current_obj_expr.id() == ID_dereference &&
           current_obj_expr.operands()[0].id() == ID_address_of) ||
          (current_obj_expr.id() == ID_address_of &&
           current_obj_expr.operands()[0].id() == ID_dereference))
      current_obj_expr = current_obj_expr.operands()[0].operands()[0];
    // buf->a --translated--> (*buf).a
    if(current_obj_expr.id() == ID_dereference)
    {
      INVARIANT(
        current_obj_expr.operands().size() == 1,
        "dereference should only have one operand");
      const exprt &pointer = current_obj_expr.operands()[0]; // buf
      irep_idt pointer_str_id = get_string_id_from_exprt(pointer);
      return std::string(pointer_str_id.c_str()) + "->" +
             std::string(comp_name.c_str());
    }
    else // buf.a
    {
      irep_idt obj_str_id = get_string_id_from_exprt(current_obj_expr); // buf
      return std::string(obj_str_id.c_str()) + "." +
             std::string(comp_name.c_str());
    }
  }
  else
  {
    throw "cannot translate to string id for expression " +
      std::string(expr.id().c_str());
  }
}

// check if an expr is a entity
// e.g. a, b, a.len, b->len are all entities
// *buf_p.len is a entity,
// but *(buf_p+1).len is not considered as one
bool rrat::is_entity_expr(const exprt &expr)
{
  if(expr.id() == ID_symbol)
  {
    return true;
  }
  else if(expr.id() == ID_member)
  {
    INVARIANT(
      expr.operands().size() == 1,
      "member access should only have one operand");
    const exprt &obj_expr = expr.operands()[0];

    // we need to get rid of dereference/address_of pairs
    // e.g. *&*&buf
    exprt current_obj_expr = obj_expr;
    while((current_obj_expr.id() == ID_dereference &&
           current_obj_expr.operands()[0].id() == ID_address_of) ||
          (current_obj_expr.id() == ID_address_of &&
           current_obj_expr.operands()[0].id() == ID_dereference))
      current_obj_expr = current_obj_expr.operands()[0].operands()[0];
    // buf->a --translated--> (*buf).a
    if(current_obj_expr.id() == ID_dereference)
    {
      INVARIANT(
        current_obj_expr.operands().size() == 1,
        "dereference should only have one operand");
      const exprt &pointer = current_obj_expr.operands()[0]; // buf
      return is_entity_expr(pointer);
    }
    else // buf.a
    {
      return is_entity_expr(current_obj_expr);
    }
  }
  else
  {
    return false;
  }
}

std::pair<std::string, irep_idt> rrat::get_parent_id(const irep_idt &id)
{
  std::string id_str = id.c_str();
  size_t arrow_pos = id_str.rfind("->");
  size_t point_pos = id_str.rfind(".");
  if(arrow_pos != std::string::npos && point_pos != std::string::npos)
  {
    if(arrow_pos > point_pos) // should be "->"
      return std::make_pair("->", id_str.substr(0, arrow_pos));
    else // should be "."
      return std::make_pair(".", id_str.substr(0, point_pos));
  }
  else if(arrow_pos == std::string::npos && point_pos != std::string::npos)
  {
    // should be "."
    return std::make_pair(".", id_str.substr(0, point_pos));
  }
  else if(arrow_pos != std::string::npos && point_pos == std::string::npos)
  {
    // should be "->"
    return std::make_pair("->", id_str.substr(0, arrow_pos));
  }
  else // both "->" and "." are not found
  {
    return std::make_pair("", irep_idt(""));
  }
}

void rrat::link_abst_functions(
  goto_modelt &goto_model,
  const rra_spect &abst_spec,
  ui_message_handlert &msg_handler,
  const optionst &options)
{
  // get abst function file names
  std::vector<std::string> abstfiles =
    abst_spec.get_abstraction_function_files();
  // read files
  goto_modelt goto_model_for_abst_fns =
    initialize_goto_model(abstfiles, msg_handler, options);
  // link goto model
  link_goto_model(goto_model, goto_model_for_abst_fns, msg_handler);
}

std::unordered_set<irep_idt> rrat::update_relation_graph_from_function(
  const goto_functiont &goto_function,
  rrat::expr_type_relationt &etr,
  goto_modelt &goto_model)
{
  std::unordered_set<irep_idt> funcs_called;
  forall_goto_program_instructions(it, goto_function.body)
  {
    // go through conditions
    if(it->has_condition())
    {
      etr.add_expr(it->get_condition());
    }

    // go through all expressions
    if(it->is_function_call())
    {
      const code_function_callt fc = it->get_function_call();
      exprt new_lhs = fc.lhs();
      etr.add_expr(fc.lhs());

      const irep_idt &new_func_name =
        to_symbol_expr(fc.function()).get_identifier();
      const goto_functiont &new_function =
        goto_model.get_goto_function(new_func_name);

      if(funcs_called.find(new_func_name) == funcs_called.end())
        funcs_called.insert(new_func_name);

      // need to build relationship between argument and parameters
      // func(a.len, b) on func(arg1, arg2) should be treated
      // in the same way as arg1=a.len, arg2=b
      for(size_t i = 0; i < fc.arguments().size(); i++)
      {
        auto arg = fc.arguments()[i];
        irep_idt param_str = new_function.parameter_identifiers[i];
        if(param_str != "")
        {
          // if param is "", it is built in functions such as malloc.
          // we need to stop
          exprt param =
            goto_model.get_symbol_table().lookup_ref(param_str).symbol_expr();
          size_t arg_id = etr.add_expr(arg);
          size_t param_id = etr.add_expr(param);
          etr.link_exprt_equiv(param_id, arg_id);
        }
      }
    }
    else if(it->is_assign())
    {
      const code_assignt as = it->get_assign();
      size_t l_id = etr.add_expr(as.lhs());
      size_t r_id = etr.add_expr(as.rhs());
      etr.link_exprt_equiv(l_id, r_id);
    }
  }
  return funcs_called;
}

/// check if an expr is address_of or dereference
/// \return flag: 0(none); 1(address_of) -1(dereference)
rra_spect::spect::func_call_arg_namet::arg_translate_typet
rrat::check_expr_is_address_or_deref(const exprt &expr, exprt &next_layer)
{
  if(expr.id() == ID_dereference)
  {
    INVARIANT(
      expr.operands().size() == 1, "dereference should only have one operand");
    next_layer = expr.operands()[0];
    return rra_spect::spect::func_call_arg_namet::POINTER_TO_ENTITY;
  }
  else if(expr.id() == ID_address_of)
  {
    INVARIANT(
      expr.operands().size() == 1, "address_of should only have one operand");
    next_layer = expr.operands()[0];
    return rra_spect::spect::func_call_arg_namet::ENTITY_TO_POINTER;
  }
  else
  {
    return rra_spect::spect::func_call_arg_namet::REGULAR;
  }
}

/// check if expr is a symbol (or typecast from a symbol)
/// \return the symbol name, "" if expr is not a symbol
irep_idt rrat::check_expr_is_symbol(const exprt &expr)
{
  if(expr.id() == ID_symbol || expr.id() == ID_member)
  {
    // if it is a symbol, return itself's name
    return get_string_id_from_exprt(expr);
  }
  else if(expr.id() == ID_typecast)
  {
    // if it is a typecast, check the next level
    // typecast are something like (char *)lhs, (size_t)a
    return check_expr_is_symbol(expr.operands()[0]);
  }
  else
  {
    // otherwise, the argument is not a symbol
    return irep_idt("");
  }
}

std::unordered_set<irep_idt> rrat::complete_the_global_abst_spec(
  goto_modelt &goto_model,
  rra_spect &abst_spec)
{
  std::unordered_set<irep_idt> all_functions;
  for(auto &spec : abst_spec.get_specs())
  {
    expr_type_relationt etr(spec);

    // The following is a search of functions.
    // At each step, we pop one function A from the todo list.
    // We analyze A to see if it calls other functions.
    // If any other functions are called and have not been analyzed,
    // we also analyze that function,
    // and then push that to the todo list.
    // Each function is only analyzed for one time.

    // functions to be further analyzed
    std::set<irep_idt> todo;
    // functions that have been analyzed
    std::unordered_set<irep_idt> finished;
    // the analysis starts from the init function
    todo.insert(abst_spec.get_func_name());

    while(!todo.empty())
    {
      // pop the first function in the todo list
      irep_idt current_func_name = *todo.begin();
      INVARIANT(
        finished.find(current_func_name) == finished.end(),
        "we should never analyze the same function twice");
      todo.erase(current_func_name);
      finished.insert(current_func_name);

      const goto_functiont &current_func =
        goto_model.get_goto_function(current_func_name);

      // check it calls any other functions that we need to abstract
      std::unordered_set<irep_idt> funcs_called =
        update_relation_graph_from_function(current_func, etr, goto_model);

      // for each function we need to abstract, check if it's already analyzed
      // if not, we analyze it and put it into the function_spec_map and todo
      for(const auto &new_func_name : funcs_called)
      {
        if(
          todo.find(new_func_name) == todo.end() &&
          finished.find(new_func_name) == finished.end())
          todo.insert(new_func_name);
      }
    }

    etr.solve();
    for(const auto &new_ent_p : etr.get_new_entities())
      if(!spec.has_entity(new_ent_p.first))
        spec.insert_entity(new_ent_p.first, new_ent_p.second);

    all_functions = finished;
  }

  return all_functions;
}

bool rrat::contains_an_entity_to_be_abstracted(
  const exprt &expr,
  const rra_spect &abst_spec)
{
  struct match_abst_symbolt
  {
    explicit match_abst_symbolt(const rra_spect &_abst_spec)
      : abst_spec(_abst_spec)
    {
    }
    // check if expr is an entity symbol that we want to abstract
    bool operator()(const exprt &expr)
    {
      irep_idt symbol_name = check_expr_is_symbol(expr);
      return symbol_name != "" && abst_spec.has_entity(symbol_name);
    }

  protected:
    // we assume this abst_spec's life span covers
    // the life span of the match_abst_symbolt object
    const rra_spect &abst_spec;
  };
  match_abst_symbolt match_abst_symbol(abst_spec);
  return has_subexpr(expr, match_abst_symbol);
}

irep_idt rrat::get_abstract_name(const irep_idt &old_name)
{
  return irep_idt(std::string(old_name.c_str()) + "$abst");
}

irep_idt rrat::get_const_c_str_len_name(const irep_idt &c_str_name)
{
  return irep_idt(std::string(c_str_name.c_str()) + "$cstrlen$abst");
}

bool rrat::contains_a_function_call(const exprt &expr)
{
  class find_functiont : public const_expr_visitort
  {
  public:
    bool found;
    find_functiont() : found(false)
    {
    }
    void operator()(const exprt &expr)
    {
      if(expr.id() == ID_symbol)
      {
        std::string symb_name(to_symbol_expr(expr).get_identifier().c_str());
        if(
          symb_name.find("$tmp") != std::string::npos &&
          symb_name.find("return_value") != std::string::npos)
          found = true;
      }
    }
  };
  find_functiont ff;
  expr.visit(ff);
  return ff.found;
}

std::vector<exprt>
rrat::get_direct_access_exprs(const exprt &expr, const rra_spect::spect &spec)
{
  class find_direct_accesst : public const_expr_visitort
  {
  protected:
    const irep_idt target_array;
    std::vector<exprt> direct_accesses;

  public:
    explicit find_direct_accesst(const irep_idt &_target_array)
      : target_array(_target_array)
    {
    }
    void operator()(const exprt &expr)
    {
      if(expr.id() == ID_dereference)
      {
        INVARIANT(
          expr.operands().size() == 1,
          "dereference should only have one operand");
        const exprt pointer_expr = expr.operands()[0];
        if(
          pointer_expr.id() == ID_plus &&
          pointer_expr.operands().front().id() == ID_symbol &&
          pointer_expr.operands().front().type().id() == ID_pointer)
        {
          INVARIANT(
            pointer_expr.operands().size() == 2, "plus should have 2 operands");
          const symbol_exprt &symb =
            to_symbol_expr(pointer_expr.operands().front());
          // tell if the pointer is the target one
          if(symb.get_identifier() == target_array)
            direct_accesses.push_back(pointer_expr.operands()[1]);
        }
      }
    }
    std::vector<exprt> get_direct_accesses() const
    {
      return direct_accesses;
    }
  };
  std::vector<exprt> result;
  for(const auto &array : spec.get_abst_arrays())
  {
    const irep_idt &array_name = array.first;
    const irep_idt array_name_abst = get_abstract_name(array_name);
    find_direct_accesst fda(array_name_abst);
    expr.visit(fda);
    for(const auto &e : fda.get_direct_accesses())
      result.push_back(e);
  }
  for(const auto &array : spec.get_abst_const_c_strs())
  {
    const irep_idt &array_name = array.first;
    const irep_idt array_name_abst = get_abstract_name(array_name);
    find_direct_accesst fda(array_name_abst);
    expr.visit(fda);
    for(const auto &e : fda.get_direct_accesses())
      result.push_back(e);
  }
  return result;
}

exprt rrat::add_guard_expression_to_assert(
  const exprt &expr,
  const exprt &expr_before_abst,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  if(contains_a_function_call(expr_before_abst))
  {
    const char *assertion_error =
      "the assertion contains a function call. "
      "Currently our system doesn't support it.";
    throw assertion_error;
  }
  // get all abstract indices in the assertion and create the new expr
  exprt::operandst is_precise_exprs;
  for(const auto &spec : abst_spec.get_specs())
  {
    const irep_idt is_prec_func = spec.get_precise_func();
    std::unordered_set<std::string> accesses;
    for(const exprt &index : get_direct_access_exprs(expr, spec))
    {
      // initialize the operands used by is_precise function
      exprt::operandst operands{index};
      push_concrete_indices_to_operands(operands, spec, goto_model);
      // create the function call for is_precise
      symbolt symb_precise = create_function_call(
        is_prec_func,
        operands,
        current_func,
        goto_model,
        insts_before,
        insts_after,
        new_symbs);
      typecast_exprt symb_precise_bool(
        symb_precise.symbol_expr(), bool_typet());
      is_precise_exprs.push_back(symb_precise_bool);
      if(accesses.find(index.pretty()) == accesses.end())
        accesses.insert(index.pretty());
    }
    INVARIANT(
      1 + accesses.size() + spec.get_abst_lengths().size() <=
        spec.get_shape_indices().size(),
      "We need to have at least " +
        std::to_string(1 + accesses.size() + spec.get_abst_lengths().size()) +
        " concrete indices to make sure the proof is sound");
  }

  // the final exprt should be is_prec_all->expr
  if(is_precise_exprs.size() > 0)
  {
    and_exprt is_prec_all(is_precise_exprs);
    implies_exprt final_expr(is_prec_all, expr);
    return std::move(final_expr);
  }
  else
  {
    return expr;
  }
}

void rrat::declare_abst_variables(
  goto_modelt &goto_model,
  const std::unordered_set<irep_idt> &functions,
  const rra_spect &abst_spec)
{
  symbol_tablet &symbol_table = goto_model.symbol_table;
  std::unordered_set<irep_idt> abst_var_set;

  // helper function to insert abst variables into the symbol table
  auto insert_abst_symbol =
    [&symbol_table, &abst_var_set](const rra_spect::spect::entityt &entity) {
      // sometimes vars in built in functions has no identifers
      // we don't handle those cases by default
      if(symbol_table.has_symbol(entity.entity_name()))
      {
        // insert the symbol var_name$abst into the symbol table
        const symbolt &orig_symbol =
          symbol_table.lookup_ref(entity.entity_name());
        symbolt abst_symbol(orig_symbol);
        abst_symbol.name = get_abstract_name(entity.entity_name());
        if(!symbol_table.has_symbol(abst_symbol.name))
        {
          symbol_table.insert(abst_symbol);
          abst_var_set.insert(abst_symbol.name);
        }
        else
        {
          if(abst_var_set.find(abst_symbol.name) == abst_var_set.end())
            throw "abstract variable's name already occupied.";
        }
      }
    };

  // Step 1: insert abst variables into the symbol table
  for(const rra_spect::spect &spec : abst_spec.get_specs())
  {
    for(const auto &ent_pair : spec.get_top_level_entities())
      insert_abst_symbol(ent_pair.second);
  }

  // Step 2: if it is in the function parameter list, change the name
  for(const auto &func_name : functions)
  {
    goto_functiont &function =
      goto_model.goto_functions.function_map.at(func_name);
    for(auto &param : function.parameter_identifiers)
      if(abst_spec.has_entity(param))
        param = std::string(param.c_str()) + "$abst";
    INVARIANT(
      goto_model.get_symbol_table().has_symbol(func_name),
      "The function " + std::string(func_name.c_str()) + " is not found");
    symbolt &function_symb =
      goto_model.symbol_table.get_writeable_ref(func_name);
    code_typet &function_type = to_code_type(function_symb.type);
    for(auto &param : function_type.parameters())
    {
      const irep_idt param_id = param.get_identifier();
      if(abst_spec.has_entity(param_id))
        param.set_identifier(get_abstract_name(param_id));
    }
  }

  // Note: we don't have to handle declare and dead here.
  // They'll be handled in the main run through the instructions.
}

bool rrat::check_if_exprt_eval_to_abst_index(
  const exprt &expr,
  const rra_spect &abst_spec,
  rra_spect::spect &spec)
{
  if(expr.id() == ID_symbol || expr.id() == ID_member)
  {
    // if it is a symbol, check whether if it is in the entity list
    const irep_idt symb_id = get_string_id_from_exprt(expr);
    if(abst_spec.has_index_entity(symb_id))
    {
      spec = abst_spec.get_spec_for_index_entity(symb_id);
      return true;
    }
    else
    {
      return false;
    }
  }
  else if(
    expr.id() == ID_const_cast || expr.id() == ID_static_cast ||
    expr.id() == ID_typecast || expr.id() == ID_dynamic_cast ||
    expr.id() == ID_reinterpret_cast)
  {
    // if it is a cast, we check the lower level
    if(expr.operands().size() != 1)
      throw "cast expressions should have one operand";
    return check_if_exprt_eval_to_abst_index(
      *expr.operands().begin(), abst_spec, spec);
  }
  else if(expr.id() == ID_plus || expr.id() == ID_minus)
  {
    // if it is plus or minus, it should stay the same as the abstracted operand
    if(expr.operands().size() != 2)
      throw "add/minus expressions should have two operands";
    rra_spect::spect spec1, spec2;
    bool abs1 =
      check_if_exprt_eval_to_abst_index(expr.operands()[0], abst_spec, spec1);
    bool abs2 =
      check_if_exprt_eval_to_abst_index(expr.operands()[1], abst_spec, spec2);
    if(!abs1 && !abs2)
    {
      return false;
    }
    else if(!abs1 && abs2)
    {
      spec = spec2;
      return true;
    }
    else if(abs1 && !abs2)
    {
      spec = spec1;
      return true;
    }
    else
    {
      // TODO: we may want to change that in the future
      // e.g. using abst_index1-abst_index2 might be possible in the code
      throw "direct computation on two abstracted indices are prohibited";
    }
  }
  else if(expr.id() == ID_pointer_offset || expr.id() == ID_object_size)
  {
    // if we are trying to get the offset of a pointer or
    // the size is a pointer, expr will be evaluated to abst index
    // if the pointer is an abst array
    INVARIANT(
      expr.operands().size() == 1,
      "pointer offset or object size exprs should only have one operand");
    const exprt &pointer = *expr.operands().begin();
    if(pointer.id() == ID_symbol)
    {
      if(abst_spec.has_array_entity(to_symbol_expr(pointer).get_identifier()))
      {
        // if the pointer is an abstracted array,
        // we should use the same spec of this array
        spec = abst_spec.get_spec_for_array_entity(
          to_symbol_expr(pointer).get_identifier());
        return true;
      }
      else if(abst_spec.has_const_c_str_entity(
                to_symbol_expr(pointer).get_identifier()))
      {
        // if the pointer is an abstracted array,
        // we should use the same spec of this array
        spec = abst_spec.get_spec_for_const_c_str_entity(
          to_symbol_expr(pointer).get_identifier());
        return true;
      }
      else
      {
        return false;
      }
    }
    else
    {
      const char *size_error =
        "size or offset checking on complex pointers"
        " are not supported in abstraction right now";
      throw size_error;
    }
  }
  else
  {
    return false;
  }
}

void rrat::push_concrete_indices_to_operands(
  exprt::operandst &operands,
  const rra_spect::spect &spec,
  const goto_modelt &goto_model)
{
  for(const auto &c_ind : spec.get_shape_indices())
  {
    if(!goto_model.get_symbol_table().has_symbol(c_ind))
      throw "concrete index symbol " + std::string(c_ind.c_str()) +
        " not found";
    const symbolt &c_ind_symb = goto_model.get_symbol_table().lookup_ref(c_ind);
    operands.push_back(c_ind_symb.symbol_expr());
  }
}

symbolt rrat::create_function_call(
  const irep_idt &func_name,
  const exprt::operandst operands,
  const irep_idt &caller,
  const goto_modelt &goto_model,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // determine the temp symbol's name
  std::unordered_set<irep_idt> new_symbs_name;
  for(const auto &symb : new_symbs)
    new_symbs_name.insert(symb.name);

  auto get_name = [&caller, &func_name, &goto_model, &new_symbs_name]() {
    // base name is "{caller}::$tmp::return_value_{callee}"
    std::string base_name = std::string(caller.c_str()) +
                            "::$tmp::return_value_" +
                            std::string(func_name.c_str());
    // if base name is not defined yet, use the base name
    if(
      !goto_model.symbol_table.has_symbol(irep_idt(base_name)) &&
      new_symbs_name.find(irep_idt(base_name)) == new_symbs_name.end())
      return irep_idt(base_name);

    // otherwise use "{basename}$id" with the lowest id available
    size_t id = 0;
    while(goto_model.symbol_table.has_symbol(
            irep_idt(base_name + "$" + std::to_string(id))) ||
          new_symbs_name.find(irep_idt(base_name + "$" + std::to_string(id))) !=
            new_symbs_name.end())
      id++;

    return irep_idt(base_name + "$" + std::to_string(id));
  };
  irep_idt temp_symb_name = get_name();

  // define the symbol
  symbolt new_symb;
  if(!goto_model.get_symbol_table().has_symbol(func_name))
    throw "unable to find function " + std::string(func_name.c_str()) +
      " in the symbol table";
  new_symb.type =
    to_code_type(goto_model.get_symbol_table().lookup_ref(func_name).type)
      .return_type();
  new_symb.name = temp_symb_name;
  new_symb.mode = ID_C;
  symbol_exprt new_symb_expr = new_symb.symbol_expr();
  new_symbs.push_back(new_symb);

  // instruction 1: DECLARE of the temp symbol
  auto new_decl_inst = goto_programt::make_decl(code_declt(new_symb_expr));
  insts_before.push_back(new_decl_inst);

  // instruction 2: FUNCTION_CALL
  symbol_exprt func_call_expr =
    goto_model.get_symbol_table().lookup_ref(func_name).symbol_expr();
  auto new_func_call_inst = goto_programt::make_function_call(
    code_function_callt(new_symb_expr, func_call_expr, operands));
  insts_before.push_back(new_func_call_inst);

  // instruction 3: DEAD for the temp symbol
  auto new_dead_inst = goto_programt::make_dead(new_symb_expr);
  insts_after.push_back(new_dead_inst);

  return new_symb;
}

symbolt rrat::create_temp_var_for_expr(
  const exprt &target_expr,
  const irep_idt &caller,
  const goto_modelt &goto_model,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // determine the temp symbol's name
  std::unordered_set<irep_idt> new_symbs_name;
  for(const auto &symb : new_symbs)
    new_symbs_name.insert(symb.name);

  auto get_name = [&caller, &goto_model, &new_symbs_name]() {
    // base name is "{caller}::$tmp::return_value_{callee}"
    std::string base_name =
      std::string(caller.c_str()) + "::$tmp::$abst::temp_var_for_expr";
    // if base name is not defined yet, use the base name
    if(
      !goto_model.symbol_table.has_symbol(irep_idt(base_name)) &&
      new_symbs_name.find(irep_idt(base_name)) == new_symbs_name.end())
      return irep_idt(base_name);

    // otherwise use "{basename}$id" with the lowest id available
    size_t id = 0;
    while(goto_model.symbol_table.has_symbol(
            irep_idt(base_name + "$" + std::to_string(id))) ||
          new_symbs_name.find(irep_idt(base_name + "$" + std::to_string(id))) !=
            new_symbs_name.end())
      id++;

    return irep_idt(base_name + "$" + std::to_string(id));
  };
  irep_idt temp_symb_name = get_name();

  // define the symbol
  symbolt new_symb;
  new_symb.type = target_expr.type();
  new_symb.name = temp_symb_name;
  new_symb.mode = ID_C;
  symbol_exprt new_symb_expr = new_symb.symbol_expr();
  new_symbs.push_back(new_symb);

  // instruction 1: DECLARE of the temp symbol
  auto new_decl_inst = goto_programt::make_decl(code_declt(new_symb_expr));
  insts_before.push_back(new_decl_inst);

  // instruction 2: ASSIGNMENT
  auto new_assign_inst =
    goto_programt::make_assignment(code_assignt(new_symb_expr, target_expr));
  insts_before.push_back(new_assign_inst);

  // instruction 3: DEAD for the temp symbol
  auto new_dead_inst = goto_programt::make_dead(new_symb_expr);
  insts_after.push_back(new_dead_inst);

  return new_symb;
}

symbolt rrat::create_abstract_func_after(
  const exprt &real_lhs,
  const rra_spect::spect &spec,
  const irep_idt &caller,
  const goto_modelt &goto_model,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // determine the temp lhs's name
  std::unordered_set<irep_idt> new_symbs_name;
  for(const auto &symb : new_symbs)
    new_symbs_name.insert(symb.name);

  const irep_idt &func_name = spec.get_abstract_func();
  auto get_name = [&caller, &func_name, &goto_model, &new_symbs_name]() {
    // base name is "{caller}::$tmp::before_{callee}"
    std::string base_name = std::string(caller.c_str()) + "::$tmp::before_" +
                            std::string(func_name.c_str());
    // if base name is not defined yet, use the base name
    if(
      !goto_model.symbol_table.has_symbol(irep_idt(base_name)) &&
      new_symbs_name.find(irep_idt(base_name)) == new_symbs_name.end())
      return irep_idt(base_name);

    // otherwise use "{basename}$id" with the lowest id available
    size_t id = 0;
    while(goto_model.symbol_table.has_symbol(
            irep_idt(base_name + "$" + std::to_string(id))) ||
          new_symbs_name.find(irep_idt(base_name + "$" + std::to_string(id))) !=
            new_symbs_name.end())
      id++;

    return irep_idt(base_name + "$" + std::to_string(id));
  };
  irep_idt temp_symb_name = get_name();

  // define the symbol
  symbolt temp_lhs_symb;
  temp_lhs_symb.type = real_lhs.type();
  temp_lhs_symb.name = temp_symb_name;
  temp_lhs_symb.mode = ID_C;
  symbol_exprt temp_lhs_expr = temp_lhs_symb.symbol_expr();
  new_symbs.push_back(temp_lhs_symb);

  // instruction 1: DECLARE of the temp symbol
  auto new_decl_inst = goto_programt::make_decl(code_declt(temp_lhs_expr));
  insts_before.push_back(new_decl_inst);

  // instruction 2: FUNCTION_CALL
  symbol_exprt func_call_expr =
    goto_model.get_symbol_table().lookup_ref(func_name).symbol_expr();
  exprt::operandst operands{temp_lhs_expr};
  push_concrete_indices_to_operands(operands, spec, goto_model);
  auto new_func_call_inst = goto_programt::make_function_call(
    code_function_callt(real_lhs, func_call_expr, operands));
  insts_after.push_back(new_func_call_inst);

  // instruction 3: DEAD for the temp symbol
  auto new_dead_inst = goto_programt::make_dead(temp_lhs_expr);
  insts_after.push_back(new_dead_inst);

  return temp_lhs_symb;
}

exprt rrat::abstract_expr_write(
  const exprt &expr,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  if(!contains_an_entity_to_be_abstracted(expr, abst_spec))
    return expr;

  if(expr.id() == ID_symbol)
  {
    // if it is a symbol, we just return the new abstract symbol
    const symbol_exprt &symb = to_symbol_expr(expr);
    irep_idt new_name = get_abstract_name(symb.get_identifier());
    if(goto_model.symbol_table.has_symbol(new_name))
    {
      symbol_exprt new_symb_expr =
        goto_model.symbol_table.lookup_ref(new_name).symbol_expr();
      return std::move(new_symb_expr);
    }
    else
    {
      std::string error_code = "Abst variable " +
                               std::string(new_name.c_str()) +
                               " used before inserting to the symbol table";
      throw error_code;
    }
  }
  else if(expr.id() == ID_member)
  {
    // if it is a member access, we should run abst read on the object
    INVARIANT(
      expr.operands().size() == 1,
      "member access should only have one operand");
    const member_exprt &mem_expr = to_member_expr(expr);
    const exprt &obj_expr = expr.operands()[0];
    const irep_idt &comp_name = mem_expr.get_component_name();

    exprt new_obj_expr = abstract_expr_write(
      obj_expr,
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);

    member_exprt new_mem_expr(new_obj_expr, comp_name, mem_expr.type());
    return std::move(new_mem_expr);
  }
  else if(expr.id() == ID_dereference) // e.g. c_str[i] => *(c_str+i)
  {
    INVARIANT(
      expr.operands().size() == 1, "dereference should only have 1 operand");
    const exprt &pointer_expr = expr.operands()[0];
    if(pointer_expr.id() == ID_plus && pointer_expr.type().id() == ID_pointer)
    {
      INVARIANT(
        pointer_expr.operands().size() == 2, "plus should have 2 operands");
      if(
        pointer_expr.operands()[0].id() == ID_symbol &&
        pointer_expr.operands()[0].type().id() == ID_pointer)
      {
        const symbol_exprt &a = to_symbol_expr(pointer_expr.operands()[0]);
        const exprt &i = pointer_expr.operands()[1];
        // we have 4 different cases: a$abst[i$abst], a[i$abst], a$abst[i], a[i]
        rra_spect::spect a_spec;
        INVARIANT(
          !abst_spec.has_const_c_str_entity(a.get_identifier()),
          "We shouldn't write to a const c string entity. Entity: " +
            std::string(a.get_identifier().c_str()));
        bool a_abs = abst_spec.has_array_entity(a.get_identifier());
        if(a_abs)
          a_spec = abst_spec.get_spec_for_array_entity(a.get_identifier());
        rra_spect::spect i_spec;
        bool i_abs = check_if_exprt_eval_to_abst_index(i, abst_spec, i_spec);

        auto new_a = abstract_expr_write(
          a,
          abst_spec,
          goto_model,
          current_func,
          insts_before,
          insts_after,
          new_symbs);
        auto new_i = abstract_expr_read(
          i,
          abst_spec,
          goto_model,
          current_func,
          insts_before,
          insts_after,
          new_symbs);
        exprt new_pointer_expr(pointer_expr);
        exprt new_expr(expr);

        if(a_abs && i_abs)
        {
          // a[i] ==> a$abst[i$abst]
          // actually it should be is_precise(i$abst)?a$abst[i$abst]:null
          // but writing to an abstract location doesn't matter
          if(!a_spec.compare_shape(i_spec))
            throw "array and index in array[index] not using the same shape";
          new_pointer_expr.operands()[0] = new_a;
          new_pointer_expr.operands()[1] = new_i;
          new_expr.operands()[0] = new_pointer_expr;
          return new_expr;
        }
        else if(!a_abs && i_abs)
        {
          // a[i] ==> a[concretize(i)]
          const irep_idt &conc_func = i_spec.get_concretize_func();
          exprt::operandst operands{new_i};
          // put the concrete indices into operands
          push_concrete_indices_to_operands(operands, i_spec, goto_model);
          // make the function call
          auto new_i_symb = create_function_call(
            conc_func,
            operands,
            current_func,
            goto_model,
            insts_before,
            insts_after,
            new_symbs);
          new_pointer_expr.operands()[0] = new_a;
          new_pointer_expr.operands()[1] = new_i_symb.symbol_expr();
          new_expr.operands()[0] = new_pointer_expr;
          return new_expr;
        }
        else if(a_abs && !i_abs)
        {
          // a[i] ==> a$abst[abst(i)]
          const irep_idt &abst_func = a_spec.get_abstract_func();
          exprt::operandst operands{new_i};
          // put the concrete indices into operands
          push_concrete_indices_to_operands(operands, a_spec, goto_model);
          // make the function call
          auto new_i_symb = create_function_call(
            abst_func,
            operands,
            current_func,
            goto_model,
            insts_before,
            insts_after,
            new_symbs);
          new_pointer_expr.operands()[0] = new_a;
          new_pointer_expr.operands()[1] = new_i_symb.symbol_expr();
          new_expr.operands()[0] = new_pointer_expr;
          return new_expr;
        }
        else // !a_abs && !i_abs
        {
          // a[i] ==> a[i]
          new_pointer_expr.operands()[0] = new_a;
          new_pointer_expr.operands()[1] = new_i;
          new_expr.operands()[0] = new_pointer_expr;
          return new_expr;
        }
      }
      else
      {
        throw "unknown plus expression as lhs";
      }
    }
    else if(pointer_expr.id() == ID_symbol || pointer_expr.id() == ID_member)
    {
      exprt new_pointer_expr = abstract_expr_write(
        pointer_expr,
        abst_spec,
        goto_model,
        current_func,
        insts_before,
        insts_after,
        new_symbs);
      dereference_exprt new_expr(new_pointer_expr);
      return std::move(new_expr);
    }
    else
    {
      throw "unknown dereference expression as lhs";
    }
  }
  else
  {
    // This is an unknown lhs.
    std::string error_code = "";
    error_code += "Currently, " + std::string(expr.id().c_str()) +
                  "cannot be abstracted as lhs.";
    throw error_code;
  }
}

exprt rrat::create_comparator_expr_abs_abs(
  const exprt &orig_expr,
  const rra_spect::spect &spec,
  const goto_modelt &goto_model,
  const irep_idt &caller,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // create the function call is_abst(op0)
  irep_idt is_prec_func = spec.get_precise_func();
  exprt::operandst operands{orig_expr.operands()[0]};
  push_concrete_indices_to_operands(operands, spec, goto_model);
  symbolt is_prec_symb = create_function_call(
    is_prec_func,
    operands,
    caller,
    goto_model,
    insts_before,
    insts_after,
    new_symbs);

  // create the expr
  // op0==op1 ? (is_precise(op0) ? orig_expr : non_det) : orig_expr
  // we allow users to create custom plus/minus functions,
  // but we use built-in comparator function for comparing two abst indices
  // this is fine because we think this would work for most common shapes
  // such as "*c*", "*c*c*", etc.
  equal_exprt eq_expr_0(orig_expr.operands()[0], orig_expr.operands()[1]);
  typecast_exprt eq_expr(eq_expr_0, bool_typet());
  typecast_exprt is_prec_expr(is_prec_symb.symbol_expr(), bool_typet());
  if_exprt t_expr(
    is_prec_expr,
    orig_expr,
    side_effect_expr_nondett(bool_typet(), source_locationt()));
  if_exprt result_expr(eq_expr, t_expr, orig_expr);
  return std::move(result_expr);
}

exprt rrat::abstract_expr_read_comparator(
  const exprt &expr,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // handle comparators, need to call functions if
  // needed based on whether each operands are abstract
  INVARIANT(
    expr.id() == ID_le || expr.id() == ID_lt || expr.id() == ID_ge ||
      expr.id() == ID_gt || expr.id() == ID_equal || expr.id() == ID_notequal,
    "type of expr does not match abst_read_comparator");
  INVARIANT(
    expr.operands().size() == 2, "number of ops should be 2 for comparators");

  rra_spect::spect spec0;
  rra_spect::spect spec1;

  bool abs0 = false;
  bool abs1 = false;
  if(
    expr.operands()[0].id() == ID_pointer_offset ||
    expr.operands()[1].id() == ID_object_size ||
    expr.operands()[0].id() == ID_object_size)
  {
    // this is the case when we are checking out of bound access to arrays,
    // we shouldn't treat the comparison as abstract
    // TODO: this is an adhoc pattern matching fix
    //       for the built in CBMC readable assertions
    abs0 = false;
    abs1 = false;
  }
  else
  {
    abs0 =
      check_if_exprt_eval_to_abst_index(expr.operands()[0], abst_spec, spec0);
    abs1 =
      check_if_exprt_eval_to_abst_index(expr.operands()[1], abst_spec, spec1);
  }

  if(!abs0 && !abs1)
  {
    // if none of op0 and op1 is abstract index, just do plain comparision.
    exprt new_expr(expr);
    new_expr.operands()[0] = abstract_expr_read(
      expr.operands()[0],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    new_expr.operands()[1] = abstract_expr_read(
      expr.operands()[1],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    return new_expr;
  }
  else if(abs0 && abs1)
  {
    // if both of them is abstract index, we should do
    // non-det comparison if they are at the same abst value
    exprt new_expr(expr);
    if(!spec0.compare_shape(spec1))
      throw "two operands of a comparator is not of the same spect";
    new_expr.operands()[0] = abstract_expr_read(
      expr.operands()[0],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    new_expr.operands()[1] = abstract_expr_read(
      expr.operands()[1],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    if(new_expr.operands()[0].type().id() != new_expr.operands()[1].type().id())
    {
      // this can happen in the pointer_offset > 0 case
      // because pointer_offset is not size_t
      new_expr.operands()[1] =
        typecast_exprt(new_expr.operands()[1], new_expr.operands()[0].type());
    }
    return create_comparator_expr_abs_abs(
      new_expr,
      spec0,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
  }
  else if(abs0 && !abs1)
  {
    // we need to make op1 abstract before
    // calling create_comparator_expr_abs_abs
    exprt new_expr(expr);
    irep_idt abst_func = spec0.get_abstract_func();
    exprt::operandst operands{abstract_expr_read(
      expr.operands()[1],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs)};
    push_concrete_indices_to_operands(operands, spec0, goto_model);
    symbolt op1_abst_symb = create_function_call(
      abst_func,
      operands,
      current_func,
      goto_model,
      insts_before,
      insts_after,
      new_symbs);
    new_expr.operands()[0] = abstract_expr_read(
      expr.operands()[0],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    new_expr.operands()[1] = op1_abst_symb.symbol_expr();
    if(new_expr.operands()[0].type().id() != new_expr.operands()[1].type().id())
    {
      // this can happen in the pointer_offset > 0 case
      // because pointer_offset is not size_t
      new_expr.operands()[1] =
        typecast_exprt(new_expr.operands()[1], new_expr.operands()[0].type());
    }
    return create_comparator_expr_abs_abs(
      new_expr,
      spec0,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
  }
  else // !abs0 && abs1
  {
    // we need to make op0 abstract before
    // calling create_comparator_expr_abs_abs
    exprt new_expr(expr);
    irep_idt abst_func = spec1.get_abstract_func();
    exprt::operandst operands{abstract_expr_read(
      expr.operands()[0],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs)};
    push_concrete_indices_to_operands(operands, spec1, goto_model);
    symbolt op0_abst_symb = create_function_call(
      abst_func,
      operands,
      current_func,
      goto_model,
      insts_before,
      insts_after,
      new_symbs);
    new_expr.operands()[0] = op0_abst_symb.symbol_expr();
    if(new_expr.operands()[0].type().id() != new_expr.operands()[1].type().id())
    {
      // this can happen in the pointer_offset > 0 case
      // because pointer_offset is not size_t
      new_expr.operands()[0] =
        typecast_exprt(new_expr.operands()[0], new_expr.operands()[1].type());
    }
    new_expr.operands()[1] = abstract_expr_read(
      expr.operands()[1],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    return create_comparator_expr_abs_abs(
      new_expr,
      spec1,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
  }
}

// check whether an expr is a pointer offset
bool rrat::is_pointer_offset(const exprt &expr)
{
  if(expr.id() == ID_pointer_offset)
  {
    return true;
  }
  else if(expr.id() == ID_typecast)
  {
    INVARIANT(
      expr.operands().size() == 1, "typecast should only have one operand");
    return is_pointer_offset(expr.operands()[0]);
  }
  else
  {
    return false;
  }
}

exprt rrat::abstract_expr_read_plusminus(
  const exprt &expr,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  // handle plus/minus, should call plus/minus function if needed
  INVARIANT(
    expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult,
    "abst_read_plus_minus should get +, - or * exprs");
  INVARIANT(
    expr.operands().size() == 2,
    "The number of operands should be 2 for plus/minus/mult");

  rra_spect::spect spec0;
  rra_spect::spect spec1;
  bool abs0 =
    check_if_exprt_eval_to_abst_index(expr.operands()[0], abst_spec, spec0);
  bool abs1 =
    check_if_exprt_eval_to_abst_index(expr.operands()[1], abst_spec, spec1);
  if(!abs0 && !abs1)
  {
    exprt new_expr(expr);
    new_expr.operands()[0] = abstract_expr_read(
      expr.operands()[0],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    new_expr.operands()[1] = abstract_expr_read(
      expr.operands()[1],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    return new_expr;
  }
  else if((!abs0 && abs1) || (abs0 && !abs1))
  {
    // couldn't do conc-abs
    if(!abs0 && abs1 && expr.id() == ID_minus)
      throw "we couldn't do concrete_index-abst_index right now";

    // what is the spec we are using?
    const rra_spect::spect &spec = abs0 ? spec0 : spec1;
    // find the func name for the calculation
    const irep_idt &calc_func_name =
      expr.id() == ID_plus ? spec.get_addition_func()
                           : (expr.id() == ID_minus ? spec.get_minus_func()
                                                    : spec.get_multiply_func());
    // define the operands {abs, num}
    exprt op0 = abstract_expr_read(
      abs0 ? expr.operands()[0] : expr.operands()[1],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    exprt op1 = abs0 ? expr.operands()[1] : expr.operands()[0];
    exprt::operandst operands{op0, op1};
    // put the concrete indices into operands
    push_concrete_indices_to_operands(operands, spec, goto_model);
    // make the function call
    symbolt temp_var = create_function_call(
      calc_func_name,
      operands,
      current_func,
      goto_model,
      insts_before,
      insts_after,
      new_symbs);
    return std::move(temp_var.symbol_expr());
  }
  else
  {
    // this happens when we are doing pointer_offset + n$abst
    // we can simply do the original addition
    if(
      is_pointer_offset(expr.operands()[0]) ||
      is_pointer_offset(expr.operands()[1]))
    {
      exprt new_expr(expr);
      new_expr.operands()[0] = abstract_expr_read(
        expr.operands()[0],
        abst_spec,
        goto_model,
        current_func,
        insts_before,
        insts_after,
        new_symbs);
      new_expr.operands()[1] = abstract_expr_read(
        expr.operands()[1],
        abst_spec,
        goto_model,
        current_func,
        insts_before,
        insts_after,
        new_symbs);
      return new_expr;
    }
    else // otherwise this is an error
    {
      throw "direct computation on two abstracted indices are prohibited";
    }
  }
}

exprt rrat::abstract_expr_read_dereference(
  const exprt &expr,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  INVARIANT(
    expr.id() == ID_dereference,
    "abstract_expr_read_dereference should get dereference exprs");
  INVARIANT(
    expr.operands().size() == 1,
    "The number of operands should be 1 for dereference");

  // the pointer to be dereferenced
  exprt pointer_expr = expr.operands()[0];

  if(pointer_expr.id() == ID_symbol)
  {
    const symbol_exprt pointer_symb_expr = to_symbol_expr(pointer_expr);
    const irep_idt orig_name = pointer_symb_expr.get_identifier();
    if(abst_spec.has_entity(orig_name))
    {
      const irep_idt new_name = get_abstract_name(orig_name);
      if(!goto_model.symbol_table.has_symbol(new_name))
        throw "the abst symbol " + std::string(new_name.c_str()) +
          " is not added to the symbol table";
      const symbolt &abst_symb = goto_model.symbol_table.lookup_ref(new_name);
      dereference_exprt new_expr(abst_symb.symbol_expr());
      return std::move(new_expr);
    }
    else
    {
      return expr;
    }
  }
  else if(pointer_expr.id() == ID_address_of)
  {
    // we should by pass the *& pair
    INVARIANT(
      pointer_expr.operands().size() == 1,
      "address_of should only have one operand");
    return abstract_expr_read(
      pointer_expr.operands()[0],
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
  }
  else if(pointer_expr.id() == ID_plus)
  {
    // TODO: we only handle the case for a$abst[i$abst].
    // There can be other cases: a[i$abst], a$abst[i], a[i].
    INVARIANT(
      pointer_expr.operands().size() == 2,
      "The number of operands should be 2 for plus/minus");
    const exprt &base_pointer = pointer_expr.operands()[0];
    const exprt &offset_expr = pointer_expr.operands()[1];
    if(
      (base_pointer.id() == ID_symbol || base_pointer.id() == ID_member) &&
      base_pointer.type().id() == ID_pointer)
    {
      const irep_idt base_pointer_orig_name =
        get_string_id_from_exprt(base_pointer);
      const exprt new_base_pointer = abstract_expr_read(
        base_pointer,
        abst_spec,
        goto_model,
        current_func,
        insts_before,
        insts_after,
        new_symbs);
      if(
        abst_spec.has_array_entity(base_pointer_orig_name) ||
        abst_spec.has_const_c_str_entity(base_pointer_orig_name))
      {
        // a[i]  ==>   is_prec(i$abst) ? a$abst[i$abst] : nondet

        // get the array's spec
        const auto &spec =
          abst_spec.has_array_entity(base_pointer_orig_name)
            ? abst_spec.get_spec_for_array_entity(base_pointer_orig_name)
            : abst_spec.get_spec_for_const_c_str_entity(base_pointer_orig_name);

        // get the new offset i$abst
        exprt new_offset = abstract_expr_read(
          offset_expr,
          abst_spec,
          goto_model,
          current_func,
          insts_before,
          insts_after,
          new_symbs);
        rra_spect::spect i_spec;
        bool i_abs =
          check_if_exprt_eval_to_abst_index(offset_expr, abst_spec, i_spec);
        if(i_abs)
        {
          INVARIANT(
            spec.compare_shape(i_spec),
            "The shapes of the array and index in a[i] don't match");
        }
        else
        {
          // need to run abstract on i
          const irep_idt abst_func = spec.get_abstract_func();
          exprt::operandst operands{new_offset};
          // put the concrete indices into operands
          push_concrete_indices_to_operands(operands, spec, goto_model);
          // make the function call
          auto new_offset_symb = create_function_call(
            abst_func,
            operands,
            current_func,
            goto_model,
            insts_before,
            insts_after,
            new_symbs);
          new_offset = new_offset_symb.symbol_expr();
        }

        // the access a$abst[i$abst]
        plus_exprt new_plus_expr(new_base_pointer, new_offset);
        dereference_exprt new_access(new_plus_expr);

        // the function call is_prec(i$abst)
        exprt::operandst operands{new_offset};
        push_concrete_indices_to_operands(operands, spec, goto_model);
        const symbolt is_prec_symb = create_function_call(
          spec.get_precise_func(),
          operands,
          current_func,
          goto_model,
          insts_before,
          insts_after,
          new_symbs);
        const exprt is_prec = is_prec_symb.symbol_expr();
        const typecast_exprt is_prec_bool(is_prec, bool_typet());

        // the final expression is_prec(i$abst) ? a$abst[i$abst] : nondet
        if_exprt final_expr(
          is_prec_bool,
          new_access,
          side_effect_expr_nondett(expr.type(), source_locationt()));

        if(abst_spec.has_const_c_str_entity(base_pointer_orig_name))
        {
          // if i is at the concrete first '0' location, the result must be '0'
          // if i is smaller than the concrete first '0' location,
          // the result must not be '0'
          // essentially it's adding two instructions before this
          // tmp_result = is_prec(i$abst) ? a$abst[i$abst] : nondet
          // assumption(i$abst == first_0 =>
          //            tmp_result == '\0' && i$abst < first_0 =>
          //            tmp_result != '\0')
          // a[i] ==> tmp_result

          // tmp_result = is_prec(i$abst) ? a$abst[i$abst] : nondet
          symbolt tmp_result = create_temp_var_for_expr(
            final_expr,
            current_func,
            goto_model,
            insts_before,
            insts_after,
            new_symbs);

          // add assumption(i$abst == c_str_len =>
          //                tmp_result == '\0' && i$abst < c_str_len =>
          //                tmp_result != '\0')
          // get the length variable for the const c str
          INVARIANT(
            goto_model.symbol_table.has_symbol(
              get_const_c_str_len_name(base_pointer_orig_name)),
            "The const c string variable is not found in the symbol table");
          const exprt c_str_len =
            goto_model.symbol_table
              .lookup_ref(get_const_c_str_len_name(base_pointer_orig_name))
              .symbol_expr();
          const exprt new_offset_t =
            typecast_exprt(new_offset, c_str_len.type());
          const auto zero = zero_initializer(
            tmp_result.type,
            source_locationt(),
            namespacet(goto_model.symbol_table));
          CHECK_RETURN(zero.has_value());
          const exprt first_constraint = implies_exprt(
            equal_exprt(new_offset_t, c_str_len),
            equal_exprt(tmp_result.symbol_expr(), *zero));
          const exprt second_constraint = implies_exprt(
            binary_relation_exprt(new_offset_t, ID_lt, c_str_len),
            notequal_exprt(tmp_result.symbol_expr(), *zero));
          const exprt constraint =
            and_exprt(first_constraint, second_constraint);
          auto c_str_assume_inst = goto_programt::make_assumption(constraint);
          insts_before.push_back(c_str_assume_inst);
          // return tmp_result
          return tmp_result.symbol_expr();
        }
        else
        {
          return std::move(final_expr);
        }
      }
      else
      {
        exprt new_offset = abstract_expr_read(
          offset_expr,
          abst_spec,
          goto_model,
          current_func,
          insts_before,
          insts_after,
          new_symbs);

        rra_spect::spect i_spec;
        bool i_abs =
          check_if_exprt_eval_to_abst_index(offset_expr, abst_spec, i_spec);
        if(i_abs)
        {
          // need to run concretize on i
          const irep_idt abst_func = i_spec.get_concretize_func();
          exprt::operandst operands{new_offset};
          // put the concrete indices into operands
          push_concrete_indices_to_operands(operands, i_spec, goto_model);
          // make the function call
          auto new_offset_symb = create_function_call(
            abst_func,
            operands,
            current_func,
            goto_model,
            insts_before,
            insts_after,
            new_symbs);
          new_offset = new_offset_symb.symbol_expr();
        }
        else
        {
        } // don't need to do anything

        plus_exprt new_plus_expr(new_base_pointer, new_offset);
        dereference_exprt new_expr(new_plus_expr);
        return std::move(new_expr);
      }
    }
    else
    {
      throw "unknown type of dereference";
    }
  }
  else
  {
    throw "unknown type to be dereferenced: " +
      std::string(pointer_expr.id().c_str());
  }
}

exprt rrat::abstract_expr_read_index(
  const exprt &expr,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  INVARIANT(
    expr.id() == ID_index, "abstract_expr_read_index should get index exprs");
  INVARIANT(
    expr.operands().size() == 2,
    "The number of operands should be 2 for index");

  const exprt &array = expr.operands()[0];
  const exprt &index = expr.operands()[1];
  if(
    (array.id() == ID_symbol || array.id() == ID_member) &&
    array.type().id() == ID_array)
  {
    const irep_idt array_orig_name = get_string_id_from_exprt(array);
    const exprt new_array = abstract_expr_read(
      array,
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    if(
      abst_spec.has_array_entity(array_orig_name) ||
      abst_spec.has_const_c_str_entity(array_orig_name))
    {
      // a[i]  ==>   is_prec(i$abst) ? a$abst[i$abst] : nondet

      // get the array's spec
      const auto &spec =
        abst_spec.has_array_entity(array_orig_name)
          ? abst_spec.get_spec_for_array_entity(array_orig_name)
          : abst_spec.get_spec_for_const_c_str_entity(array_orig_name);

      // get the new offset i$abst
      exprt new_index = abstract_expr_read(
        index,
        abst_spec,
        goto_model,
        current_func,
        insts_before,
        insts_after,
        new_symbs);
      rra_spect::spect i_spec;
      bool i_abs = check_if_exprt_eval_to_abst_index(index, abst_spec, i_spec);
      if(i_abs)
      {
        INVARIANT(
          spec.compare_shape(i_spec),
          "The shapes of the array and index in a[i] don't match");
      }
      else
      {
        // need to run abstract on i
        const irep_idt abst_func = spec.get_abstract_func();
        exprt::operandst operands{new_index};
        // put the concrete indices into operands
        push_concrete_indices_to_operands(operands, spec, goto_model);
        // make the function call
        auto new_index_symb = create_function_call(
          abst_func,
          operands,
          current_func,
          goto_model,
          insts_before,
          insts_after,
          new_symbs);
        new_index = new_index_symb.symbol_expr();
      }

      // the access a$abst[i$abst]
      index_exprt new_access(new_array, new_index);

      // the function call is_prec(i$abst)
      exprt::operandst operands{new_index};
      push_concrete_indices_to_operands(operands, spec, goto_model);
      const symbolt is_prec_symb = create_function_call(
        spec.get_precise_func(),
        operands,
        current_func,
        goto_model,
        insts_before,
        insts_after,
        new_symbs);
      const exprt is_prec = is_prec_symb.symbol_expr();
      const typecast_exprt is_prec_bool(is_prec, bool_typet());

      // the final expression is_prec(i$abst) ? a$abst[i$abst] : nondet
      if_exprt final_expr(
        is_prec_bool,
        new_access,
        side_effect_expr_nondett(expr.type(), source_locationt()));

      if(abst_spec.has_const_c_str_entity(array_orig_name))
      {
        // if i is at the concrete first '0' location, the result must be '0'
        // if i is smaller than the concrete first '0' location,
        // the result must not be '0'
        // essentially it's adding two instructions before this
        // tmp_result = is_prec(i$abst) ? a$abst[i$abst] : nondet
        // assumption(i$abst == first_0 =>
        //            tmp_result == '\0' && i$abst < first_0 =>
        //            tmp_result != '\0')
        // a[i] ==> tmp_result

        // tmp_result = is_prec(i$abst) ? a$abst[i$abst] : nondet
        symbolt tmp_result = create_temp_var_for_expr(
          final_expr,
          current_func,
          goto_model,
          insts_before,
          insts_after,
          new_symbs);

        // add assumption(i$abst == c_str_len =>
        //                tmp_result == '\0' && i$abst < c_str_len =>
        //                tmp_result != '\0')
        // get the length variable for the const c str
        INVARIANT(
          goto_model.symbol_table.has_symbol(
            get_const_c_str_len_name(array_orig_name)),
          "The const c string variable is not found in the symbol table");
        const exprt c_str_len =
          goto_model.symbol_table
            .lookup_ref(get_const_c_str_len_name(array_orig_name))
            .symbol_expr();
        const exprt new_index_t = typecast_exprt(new_index, c_str_len.type());
        const auto zero = zero_initializer(
          tmp_result.type,
          source_locationt(),
          namespacet(goto_model.symbol_table));
        CHECK_RETURN(zero.has_value());
        const exprt first_constraint = implies_exprt(
          equal_exprt(new_index_t, c_str_len),
          equal_exprt(tmp_result.symbol_expr(), *zero));
        const exprt second_constraint = implies_exprt(
          binary_relation_exprt(new_index_t, ID_lt, c_str_len),
          notequal_exprt(tmp_result.symbol_expr(), *zero));
        const exprt constraint = and_exprt(first_constraint, second_constraint);
        auto c_str_assume_inst = goto_programt::make_assumption(constraint);
        insts_before.push_back(c_str_assume_inst);
        // return tmp_result
        return tmp_result.symbol_expr();
      }
      else
      {
        return std::move(final_expr);
      }
    }

    else
    {
      exprt new_index = abstract_expr_read(
        index,
        abst_spec,
        goto_model,
        current_func,
        insts_before,
        insts_after,
        new_symbs);

      rra_spect::spect i_spec;
      bool i_abs = check_if_exprt_eval_to_abst_index(index, abst_spec, i_spec);
      if(i_abs)
      {
        // need to run concretize on i
        const irep_idt abst_func = i_spec.get_concretize_func();
        exprt::operandst operands{new_index};
        // put the concrete indices into operands
        push_concrete_indices_to_operands(operands, i_spec, goto_model);
        // make the function call
        auto new_index_symb = create_function_call(
          abst_func,
          operands,
          current_func,
          goto_model,
          insts_before,
          insts_after,
          new_symbs);
        new_index = new_index_symb.symbol_expr();
      }
      else
      {
      } // don't need to do anything

      index_exprt new_expr(new_array, new_index);
      return std::move(new_expr);
    }
  }
  else
  {
    throw "the type of the array in an index expr is incorrect";
  }
}

exprt rrat::abstract_expr_read_address_of(
  const exprt &expr,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  INVARIANT(
    expr.id() == ID_address_of,
    "abstract_expr_read_address_of should get address_of exprs");
  INVARIANT(
    expr.operands().size() == 1,
    "The number of operands should be 1 for address_of");

  const exprt &entity = expr.operands()[0];
  if(entity.id() == ID_symbol)
  {
    exprt new_entity = abstract_expr_read(
      entity,
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
    address_of_exprt new_expr(new_entity);
    return std::move(new_expr);
  }
  else
  {
    throw "we are not supporting &(address_of) for " +
      std::string(entity.id().c_str()) + " operands.";
  }
}

exprt rrat::abstract_expr_read(
  const exprt &expr,
  const rra_spect &abst_spec,
  const goto_modelt &goto_model,
  const irep_idt &current_func,
  goto_programt::instructionst &insts_before,
  goto_programt::instructionst &insts_after,
  std::vector<symbolt> &new_symbs)
{
  if(!contains_an_entity_to_be_abstracted(expr, abst_spec))
    return expr;

  if(expr.id() == ID_symbol)
  {
    // if it is a symbol, we just return the new abstract symbol
    const symbol_exprt &symb = to_symbol_expr(expr);
    irep_idt new_name = get_abstract_name(symb.get_identifier());
    if(goto_model.symbol_table.has_symbol(new_name))
    {
      symbol_exprt new_symb_expr =
        goto_model.symbol_table.lookup_ref(new_name).symbol_expr();
      return std::move(new_symb_expr);
    }
    else
    {
      std::string error_code = "Abst variable " +
                               std::string(new_name.c_str()) +
                               " used before inserting to the symbol table";
      throw error_code;
    }
  }
  else if(expr.id() == ID_member)
  {
    // if it is a member access, we should run abst read on the object
    // For example, in C: buf->length
    // in goto: member(dereference(buf), length)
    INVARIANT(
      expr.operands().size() == 1,
      "member access should only have one operand");
    const member_exprt &mem_expr = to_member_expr(expr);
    const exprt &obj_expr = expr.operands()[0];
    const irep_idt &comp_name = mem_expr.get_component_name();

    exprt new_obj_expr = abstract_expr_read(
      obj_expr,
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);

    member_exprt new_mem_expr(new_obj_expr, comp_name, mem_expr.type());
    return std::move(new_mem_expr);
  }
  else if(
    expr.id() == ID_typecast || expr.id() == ID_and || expr.id() == ID_or ||
    expr.id() == ID_xor || expr.id() == ID_not || expr.id() == ID_implies ||
    expr.id() == ID_is_invalid_pointer || expr.id() == ID_is_dynamic_object ||
    expr.id() == ID_pointer_object || expr.id() == ID_pointer_offset ||
    expr.id() == ID_object_size || expr.id() == ID_if)
  {
    // those types of exprs should not be changed,
    // just run abst_read on lower level
    exprt new_expr(expr);
    for(size_t i = 0; i < expr.operands().size(); i++)
      new_expr.operands()[i] = abstract_expr_read(
        expr.operands()[i],
        abst_spec,
        goto_model,
        current_func,
        insts_before,
        insts_after,
        new_symbs);
    return new_expr;
  }
  else if(
    expr.id() == ID_le || expr.id() == ID_lt || expr.id() == ID_ge ||
    expr.id() == ID_gt || expr.id() == ID_equal || expr.id() == ID_notequal)
  {
    // handle comparators, need to call functions if
    // needed based on whether each operands are abstract
    return abstract_expr_read_comparator(
      expr,
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
  }
  else if(expr.id() == ID_dereference)
  {
    // handle dereference, need to check the structure of lower exprts
    return abstract_expr_read_dereference(
      expr,
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
  }
  else if(expr.id() == ID_address_of)
  {
    // handle address_of, currently we only support address of symbol
    return abstract_expr_read_address_of(
      expr,
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
  }
  else if(expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult)
  {
    // handle plus/minus, should call plus/minus function if needed
    return abstract_expr_read_plusminus(
      expr,
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
  }
  else if(expr.id() == ID_index)
  {
    // handle array access for static arrays
    return abstract_expr_read_index(
      expr,
      abst_spec,
      goto_model,
      current_func,
      insts_before,
      insts_after,
      new_symbs);
  }
  else
  {
    // This type of exprt is unknown.
    std::string error_code = "";
    error_code += "Currently, " + std::string(expr.id().c_str()) +
                  " cannot be abstracted in abst_read.";
    throw error_code;
  }
}

void rrat::define_concrete_indices(
  goto_modelt &goto_model,
  const rra_spect &abst_spec)
{
  for(const auto &spec : abst_spec.get_specs())
  {
    for(const irep_idt &index : spec.get_shape_indices())
    {
      // define the "index" in the global scope
      // Step 0: Define the symbolt. what is the type/location of this variable?
      // The type should be size_t, which is unsigned_long_int_type
      // mode should be C
      unsignedbv_typet index_type = unsigned_long_int_type();
      source_locationt src_loc;
      symbolt symb;
      symb.type = index_type;
      symb.location = src_loc;
      symb.name = index;
      symb.mode = ID_C;
      symbol_exprt symb_expr = symb.symbol_expr();

      // Step 1: put it into the symbol table
      if(goto_model.symbol_table.has_symbol(index))
        throw "the concrete index variable " + std::string(index.c_str()) +
          " is already defined";
      goto_model.symbol_table.insert(std::move(symb));

      // Step 2: put it into __CPROVER_initialize
      // which is the entry function for each goto program
      goto_functionst::function_mapt::iterator fct_entry =
        goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
      CHECK_RETURN(fct_entry != goto_model.goto_functions.function_map.end());
      goto_programt &init_function = fct_entry->second.body;
      auto last_instruction = std::prev(init_function.instructions.end());
      DATA_INVARIANT(
        last_instruction->is_end_function(),
        "last instruction in function should be END_FUNCTION");
      goto_programt::instructiont new_inst = goto_programt::make_assignment(
        code_assignt(symb_expr, side_effect_expr_nondett(index_type, src_loc)));
      init_function.insert_before_swap(last_instruction, new_inst);
    }
  }
}

void rrat::define_const_c_str_lengths(
  goto_modelt &goto_model,
  const rra_spect &abst_spec)
{
  for(const auto &spec : abst_spec.get_specs())
  {
    for(auto &c_str_len_pair : spec.get_abst_const_c_strs())
    {
      irep_idt var_name = get_const_c_str_len_name(c_str_len_pair.first);

      unsignedbv_typet index_type = unsigned_long_int_type();
      source_locationt src_loc;
      symbolt symb;
      symb.type = index_type;
      symb.location = src_loc;
      symb.name = var_name;
      symb.mode = ID_C;
      symbol_exprt symb_expr = symb.symbol_expr();

      // Step 1: put it into the symbol table
      if(goto_model.symbol_table.has_symbol(var_name))
        throw "the c_str len variable " + std::string(var_name.c_str()) +
          " is already defined";
      goto_model.symbol_table.insert(std::move(symb));

      // Step 2: put it into __CPROVER_initialize
      // which is the entry function for each goto program
      goto_functionst::function_mapt::iterator fct_entry =
        goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
      CHECK_RETURN(fct_entry != goto_model.goto_functions.function_map.end());
      goto_programt &init_function = fct_entry->second.body;
      auto last_instruction = std::prev(init_function.instructions.end());
      DATA_INVARIANT(
        last_instruction->is_end_function(),
        "last instruction in function should be END_FUNCTION");
      goto_programt::instructiont new_inst = goto_programt::make_assignment(
        code_assignt(symb_expr, side_effect_expr_nondett(index_type, src_loc)));
      init_function.insert_before_swap(last_instruction, new_inst);

      // Step 3: run is_precise on the '\0' location variable
      goto_programt::instructionst insts_before, insts_after;
      std::vector<symbolt> new_symbs;
      exprt::operandst operands{symb_expr};
      // put the concrete indices into operands
      push_concrete_indices_to_operands(operands, spec, goto_model);
      auto is_prec_ret = create_function_call(
        spec.get_precise_func(),
        operands,
        INITIALIZE_FUNCTION,
        goto_model,
        insts_before,
        insts_after,
        new_symbs);
      for(auto &inst : insts_before)
      {
        last_instruction = std::prev(init_function.instructions.end());
        DATA_INVARIANT(
          last_instruction->is_end_function(),
          "last instruction in function should be END_FUNCTION");
        init_function.insert_before_swap(last_instruction, inst);
      }
      for(auto &new_symb : new_symbs)
      {
        INVARIANT(
          !goto_model.symbol_table.has_symbol(new_symb.name),
          "the c_str len variable " + std::string(new_symb.name.c_str()) +
            " is already defined");
        goto_model.symbol_table.insert(std::move(new_symb));
      }

      // Step 4: add assumption saying it must be precise
      typecast_exprt assumption_expr(is_prec_ret.symbol_expr(), bool_typet());
      auto new_assumption = goto_programt::make_assumption(assumption_expr);
      last_instruction = std::prev(init_function.instructions.end());
      DATA_INVARIANT(
        last_instruction->is_end_function(),
        "last instruction in function should be END_FUNCTION");
      init_function.insert_before_swap(last_instruction, new_assumption);

      // Step 5: insert the instructions introduced by the create function call
      for(auto &inst : insts_after)
      {
        last_instruction = std::prev(init_function.instructions.end());
        DATA_INVARIANT(
          last_instruction->is_end_function(),
          "last instruction in function should be END_FUNCTION");
        init_function.insert_before_swap(last_instruction, inst);
      }
    }
  }
}

void rrat::insert_shape_assumptions(
  goto_modelt &goto_model,
  const rra_spect &abst_spec)
{
  namespacet ns(goto_model.get_symbol_table());
  for(const auto &spec : abst_spec.get_specs())
  {
    for(const exprt &expr : spec.get_assumption_exprs(ns))
    {
      // put the assumption expr into __CPROVER_initialize
      // which is the entry function for each goto program
      goto_functionst::function_mapt::iterator fct_entry =
        goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
      CHECK_RETURN(fct_entry != goto_model.goto_functions.function_map.end());
      goto_programt &init_function = fct_entry->second.body;
      auto last_instruction = std::prev(init_function.instructions.end());
      DATA_INVARIANT(
        last_instruction->is_end_function(),
        "last instruction in function should be END_FUNCTION");

      goto_programt::instructiont new_inst =
        goto_programt::make_assumption(expr);
      init_function.insert_before_swap(last_instruction, new_inst);
    }
  }
}

void rrat::add_length_assumptions(
  goto_modelt &goto_model,
  const rra_spect &abst_spec)
{
  const namespacet ns(goto_model.get_symbol_table());
  for(const auto &spec : abst_spec.get_specs())
  {
    for(const auto &lp : spec.get_abst_lengths_with_expr(ns))
    {
      const irep_idt func_name = abst_spec.get_func_name();

      // TODO: currently we are assuming every entities in the
      // json file belong to the same function. That may not be the case.
      auto &function = goto_model.goto_functions.function_map.at(func_name);
      // if this variable is a local varible
      bool is_local = false;

      // go through each instruction in the function to find the declare
      Forall_goto_program_instructions(it, function.body)
      {
        if(it->is_decl() || it->is_assign())
        {
          irep_idt var_name;
          if(it->is_decl())
          {
            const code_declt &decl = it->get_decl();
            var_name = decl.get_identifier();
          }
          else if(it->is_assign())
          {
            const code_assignt &assn = it->get_assign();
            if(is_entity_expr(assn.lhs()))
              var_name = get_string_id_from_exprt(assn.lhs());
            else
              continue;
          }
          else
          {
            continue;
          }

          // check if this declares the symbol containing the length
          // note that this symbol can be the length variable itself
          // or a struct containing the length variable
          if(var_name == lp.first)
          {
            // need to add an assumption after this inst
            INVARIANT(
              goto_model.get_symbol_table().has_symbol(var_name),
              "Symbol " + std::string(var_name.c_str()) + " not defined");

            if(it->is_decl())
              is_local = true;

            // define the assumption instruction
            const exprt length_expr = lp.second;
            exprt::operandst assumption_exprs;
            for(const auto &conc : spec.get_shape_indices())
            {
              INVARIANT(
                goto_model.get_symbol_table().has_symbol(conc),
                "Symbol " + std::string(spec.get_length_index_name().c_str()) +
                  " not defined");
              const symbolt conc_index_expr =
                goto_model.get_symbol_table().lookup_ref(conc);
              assumption_exprs.push_back(
                equal_exprt(length_expr, conc_index_expr.symbol_expr()));
            }

            // the value of the length variable should be
            // one of the concrete indices
            or_exprt assumption_expr(assumption_exprs);
            auto new_assumption =
              goto_programt::make_assumption(assumption_expr);

            // insert it
            function.body.insert_after(it, new_assumption);
            std::cout << "Added length assumption after the decl/assign: ";
            format_rec(std::cout, assumption_expr) << std::endl;
            it++;
          }
        }
      }

      // if it is not a local variable, the assumption should be added at
      // the end of the global INITIAL function
      if(!is_local)
      {
        // find the CPROVER_INITIAL function
        goto_functionst::function_mapt::iterator fct_entry =
          goto_model.goto_functions.function_map.find(INITIALIZE_FUNCTION);
        CHECK_RETURN(fct_entry != goto_model.goto_functions.function_map.end());
        goto_programt &init_function = fct_entry->second.body;
        auto last_instruction = std::prev(init_function.instructions.end());
        DATA_INVARIANT(
          last_instruction->is_end_function(),
          "last instruction in function should be END_FUNCTION");

        // define the assumption instruction
        INVARIANT(
          goto_model.get_symbol_table().has_symbol(lp.first),
          "Symbol " + std::string(lp.first.c_str()) + " not defined");
        INVARIANT(
          goto_model.get_symbol_table().has_symbol(
            spec.get_length_index_name()),
          "Symbol " + std::string(spec.get_length_index_name().c_str()) +
            " not defined");
        // define the assumption instruction
        const exprt length_expr = lp.second;
        exprt::operandst assumption_exprs;
        for(const auto &conc : spec.get_shape_indices())
        {
          INVARIANT(
            goto_model.get_symbol_table().has_symbol(conc),
            "Symbol " + std::string(spec.get_length_index_name().c_str()) +
              " not defined");
          const symbolt conc_index_expr =
            goto_model.get_symbol_table().lookup_ref(conc);
          assumption_exprs.push_back(
            equal_exprt(length_expr, conc_index_expr.symbol_expr()));
        }

        // the value of the length variable should be
        // one of the concrete indices
        or_exprt assumption_expr(assumption_exprs);
        auto new_assumption = goto_programt::make_assumption(assumption_expr);

        // insert it
        std::cout
          << "Added length assumption in the beginning of the function: ";
        format_rec(std::cout, assumption_expr) << std::endl;
        init_function.insert_before_swap(last_instruction, new_assumption);
      }
    }
  }
}

void rrat::abstract_goto_program(goto_modelt &goto_model, rra_spect &abst_spec)
{
  // A couple of spects are initialized from the json file.
  // We should go from there and insert spects to other functions
  std::unordered_set<irep_idt> all_funcs =
    complete_the_global_abst_spec(goto_model, abst_spec);

  // Define the global concrete indices to be used
  define_concrete_indices(goto_model, abst_spec);

  // Insert the assumptions about concrete indices
  insert_shape_assumptions(goto_model, abst_spec);

  // Define the const c_string length symbols
  define_const_c_str_lengths(goto_model, abst_spec);

  // Add the assumption for len==$clen
  add_length_assumptions(goto_model, abst_spec);

  // Put the abstracted variables into the symbol table
  // Change the function parameter's name if needed
  declare_abst_variables(goto_model, all_funcs, abst_spec);

  std::cout << "=========== "
            << "Entities to be abstracted"
            << " ==========="
            << "\n";
  abst_spec.print_entities();
  for(auto &func_name : all_funcs)
  {
    std::cout << "=========== " << func_name.c_str() << " ==========="
              << "\n";
    std::cout << "----------- "
              << "Exprs containing the above entities"
              << " -----------"
              << "\n";
    goto_functiont &goto_function =
      goto_model.goto_functions.function_map.at(func_name);
    Forall_goto_program_instructions(it, goto_function.body)
    {
      // go through all expressions
      goto_programt::instructionst inst_before;
      goto_programt::instructionst inst_after;
      std::vector<symbolt> new_symbs;

      // need to backup the expr for assertion
      exprt assert_orig_expr;
      if(it->is_assert())
        assert_orig_expr = it->get_condition();

      // go through conditions
      if(it->has_condition())
      {
        if(contains_an_entity_to_be_abstracted(it->get_condition(), abst_spec))
        {
          format_rec(std::cout, it->get_condition()) << " ==abst_read==> ";
          exprt new_condition = abstract_expr_read(
            it->get_condition(),
            abst_spec,
            goto_model,
            func_name,
            inst_before,
            inst_after,
            new_symbs);
          format_rec(std::cout, new_condition) << std::endl;
          it->set_condition(new_condition);
        }
      }

      if(it->is_function_call())
      {
        const code_function_callt fc = it->get_function_call();
        exprt new_lhs;
        if(contains_an_entity_to_be_abstracted(fc.lhs(), abst_spec))
        {
          format_rec(std::cout, fc.lhs()) << " ==abst_write==> ";
          new_lhs = abstract_expr_write(
            fc.lhs(),
            abst_spec,
            goto_model,
            func_name,
            inst_before,
            inst_after,
            new_symbs);
          format_rec(std::cout, new_lhs) << std::endl;
        }
        else
        {
          new_lhs = fc.lhs();
        }

        code_function_callt::argumentst new_arguments;
        for(const auto &arg : fc.arguments())
        {
          exprt new_arg;
          if(contains_an_entity_to_be_abstracted(arg, abst_spec))
          {
            format_rec(std::cout, arg) << " ==abst_read==> ";
            new_arg = abstract_expr_read(
              arg,
              abst_spec,
              goto_model,
              func_name,
              inst_before,
              inst_after,
              new_symbs);
            format_rec(std::cout, new_arg) << std::endl;
            new_arguments.push_back(new_arg);
          }
          else
          {
            new_arguments.push_back(arg);
          }
        }

        rra_spect::spect lhs_spec;
        bool abs_lhs =
          check_if_exprt_eval_to_abst_index(fc.lhs(), abst_spec, lhs_spec);
        if(abs_lhs)
        {
          // in this case, we need to abstract the return value
          symbolt tmp_lhs = create_abstract_func_after(
            new_lhs,
            lhs_spec,
            func_name,
            goto_model,
            inst_before,
            inst_after,
            new_symbs);
          code_function_callt new_fc(
            tmp_lhs.symbol_expr(), fc.function(), new_arguments);
          it->set_function_call(new_fc);
        }
        else
        {
          code_function_callt new_fc(new_lhs, fc.function(), new_arguments);
          it->set_function_call(new_fc);
        }
      }
      else if(it->is_assign())
      {
        const code_assignt as = it->get_assign();
        exprt new_lhs;
        if(contains_an_entity_to_be_abstracted(as.lhs(), abst_spec))
        {
          format_rec(std::cout, as.lhs()) << " ==abst_write==> ";
          new_lhs = abstract_expr_write(
            as.lhs(),
            abst_spec,
            goto_model,
            func_name,
            inst_before,
            inst_after,
            new_symbs);
          format_rec(std::cout, new_lhs) << std::endl;
        }
        else
        {
          new_lhs = as.lhs();
        }

        exprt new_rhs;
        if(contains_an_entity_to_be_abstracted(as.rhs(), abst_spec))
        {
          format_rec(std::cout, as.rhs()) << " ==abst_read==> ";
          new_rhs = abstract_expr_read(
            as.rhs(),
            abst_spec,
            goto_model,
            func_name,
            inst_before,
            inst_after,
            new_symbs);
          format_rec(std::cout, new_rhs) << std::endl;
        }
        else
        {
          new_rhs = as.rhs();
        }

        // When lhs and rhs are not both abstracted, we should
        // do the translation.
        rra_spect::spect lhs_spec;
        rra_spect::spect rhs_spec;
        bool lhs_abs =
          check_if_exprt_eval_to_abst_index(as.lhs(), abst_spec, lhs_spec);
        bool rhs_abs =
          check_if_exprt_eval_to_abst_index(as.rhs(), abst_spec, rhs_spec);
        if(lhs_abs && rhs_abs)
        {
          // don't need to do anything
          // just check if those two specs match
          INVARIANT(
            lhs_spec.compare_shape(rhs_spec),
            "The shapes used in lhs and rhs in assign don't match.");
        }
        else if(lhs_abs && !rhs_abs)
        {
          // a=b ===> a$abst = abstract(b)
          const irep_idt abst_func = lhs_spec.get_abstract_func();
          exprt::operandst operands{new_rhs};
          // put the concrete indices into operands
          push_concrete_indices_to_operands(operands, lhs_spec, goto_model);
          // make the function call
          auto new_rhs_symb = create_function_call(
            abst_func,
            operands,
            func_name,
            goto_model,
            inst_before,
            inst_after,
            new_symbs);
          new_rhs = new_rhs_symb.symbol_expr();
        }
        else if(!lhs_abs && rhs_abs)
        {
          // a=b ===> a = concretize(b$abst)
          const irep_idt conc_func = rhs_spec.get_concretize_func();
          exprt::operandst operands{new_rhs};
          // put the concrete indices into operands
          push_concrete_indices_to_operands(operands, rhs_spec, goto_model);
          // make the function call
          auto new_rhs_symb = create_function_call(
            conc_func,
            operands,
            func_name,
            goto_model,
            inst_before,
            inst_after,
            new_symbs);
          new_rhs = new_rhs_symb.symbol_expr();
        }
        else
        {
        } // don't need to do anything

        code_assignt new_as(new_lhs, new_rhs);
        it->set_assign(new_as);
      }
      else if(it->is_return())
      {
        // Function will always return concrete value.
        // We need to convert them into abstract
        // values in the caller if needed.
        const code_returnt re = it->get_return();
        if(re.has_return_value())
        {
          const exprt &re_val = re.return_value();
          exprt new_re_val;
          if(contains_an_entity_to_be_abstracted(re_val, abst_spec))
          {
            format_rec(std::cout, re_val) << " ==abst_read==> ";
            new_re_val = abstract_expr_read(
              re_val,
              abst_spec,
              goto_model,
              func_name,
              inst_before,
              inst_after,
              new_symbs);
            format_rec(std::cout, new_re_val) << std::endl;
            rra_spect::spect spec;
            if(check_if_exprt_eval_to_abst_index(re_val, abst_spec, spec))
            {
              // we assume the function will always return concrete value
              // so we calculated a concrete value in this case
              const irep_idt conc_func = spec.get_concretize_func();
              exprt::operandst operands{new_re_val};
              // put the concrete indices into operands
              push_concrete_indices_to_operands(operands, spec, goto_model);
              // make the function call
              auto new_re_symb = create_function_call(
                conc_func,
                operands,
                func_name,
                goto_model,
                inst_before,
                inst_after,
                new_symbs);
              new_re_val = new_re_symb.symbol_expr();
            }
          }
          else
          {
            new_re_val = re_val;
          }
          code_returnt new_re(new_re_val);
          it->set_return(new_re);
        }
      }
      else if(it->is_assert())
      {
        // if this is assertion, we should make the condition optimistic
        format_rec(std::cout, it->get_condition()) << " ==optimistic==> ";
        exprt optim_cond = add_guard_expression_to_assert(
          it->get_condition(),
          assert_orig_expr,
          abst_spec,
          goto_model,
          func_name,
          inst_before,
          inst_after,
          new_symbs);
        format_rec(std::cout, optim_cond) << std::endl;
        it->set_condition(optim_cond);
      }
      if(it->is_decl())
      {
        // change symbol name in DECLARE instruction
        const code_declt &decl = it->get_decl();
        const symbol_tablet &symbol_table = goto_model.get_symbol_table();
        if(abst_spec.has_entity(decl.get_identifier()))
        {
          irep_idt new_name = get_abstract_name(decl.get_identifier());
          typet typ = symbol_table.lookup_ref(new_name).type;
          symbol_exprt new_symb_expr(new_name, typ);
          code_declt new_decl(new_symb_expr);
          it->set_decl(new_decl);
        }
      }
      else if(it->is_dead())
      {
        // change symbol name in DEAD instruction
        const code_deadt &dead = it->get_dead();
        const symbol_tablet &symbol_table = goto_model.get_symbol_table();
        if(abst_spec.has_entity(dead.get_identifier()))
        {
          irep_idt new_name = get_abstract_name(dead.get_identifier());
          typet typ = symbol_table.lookup_ref(new_name).type;
          symbol_exprt new_symb_expr(new_name, typ);
          code_deadt new_dead(new_symb_expr);
          it->set_dead(new_dead);
        }
      }

      // is there any unknown inst types?
      if(
        !it->is_decl() && !it->is_end_function() && !it->is_goto() &&
        !it->is_return() && !it->is_function_call() && !it->is_assert() &&
        !it->is_assign() && !it->is_assume() && !it->is_dead() &&
        !it->is_skip() && !it->is_other())
        throw "unknown instruction type " + std::to_string(it->type);

      // insert new instructions before it
      for(auto &inst : inst_before)
      {
        goto_function.body.insert_before_swap(it, inst);
        it++;
      }

      // insert new instructions after it
      for(auto &inst : inst_after)
      {
        goto_function.body.insert_after(it, inst);
        it++;
      }

      // insert new symbols to the symbol table
      for(auto &symb : new_symbs)
      {
        if(goto_model.get_symbol_table().has_symbol(symb.name))
          throw "the temp symbol " + std::string(symb.name.c_str()) +
            " is already defined";
        goto_model.symbol_table.insert(symb);
      }
    }
  }
}
