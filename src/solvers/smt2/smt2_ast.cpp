/*******************************************************************\

Module: SMT2 solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include "smt2_ast.h"
#include <deque>
#include <util/as_const.h>
#include <util/make_unique.h>
#include <util/mp_arith.h>
#include <util/range.h>

struct smt2_ast_strategyt
{
  std::function<void(const smt2_astt &)> data;
  std::function<void(const smt2_astt &)> parent;
  std::function<void(const smt2_astt &)> first_child;
  std::function<void(const smt2_astt &)> next_sibling;
};

/// Intermediary types for the \ref smt2_dfs_stackt definition
using tree_iteratort = smt2_astt::tree_implementationt::subt::const_iterator;
using stack_elementt = ranget<tree_iteratort>;

/// Stack class to help with DFS exploration of smt2_astt.
/// The stack stores an iterator for each level above the current position,
/// as well as the corresponding \c end iterator
class smt2_dfs_stackt : public std::deque<stack_elementt>
{
public:
  /// Current node if the stack is currently pointing to one, nullptr if it
  /// needs to come back to its parent.
  const smt2_astt *current_node() const
  {
    PRECONDITION(!empty());
    if(back().empty())
      return nullptr;
    return &(*back().begin());
  }

  bool has_next_sibling() const
  {
    PRECONDITION(!empty());
    auto it = back().begin();
    it++;
    return it != back().end();
  }

  /// Advance to next sibling if it exists, otherwise render the `back`
  /// element of the stack empty.
  void go_to_next_sibling()
  {
    PRECONDITION(!empty());
    back() = std::move(back()).drop(1);
  }

  const smt2_astt *parent() const
  {
    if(this->empty())
      return nullptr;
    auto it = this->end();
    (it--)--;
    return &(*it->begin());
  }
};

static void dfs(const smt2_astt &ast, const smt2_ast_strategyt &strategy)
{
  strategy.data(ast);
  auto begin = ast.read().sub.begin();
  auto end = ast.read().sub.end();
  if(begin == end)
    return;
  strategy.first_child(ast);
  smt2_dfs_stackt stack;
  stack.emplace_back(begin, end);

  while(!stack.empty())
  {
    const auto current = stack.current_node();
    INVARIANT(
      current != nullptr,
      "at each iteration of the loop, the stack should be positioned on an "
      "existing element");
    strategy.data(*current);
    const smt2_astt::tree_implementationt::subt &children = current->read().sub;
    if(!children.empty())
    {
      stack.emplace_back(children.begin(), children.end());
      strategy.first_child(*current);
    }
    else
    {
      if(stack.has_next_sibling())
      {
        auto p = stack.parent();
        INVARIANT(p, "siblings must have a parent");
        strategy.next_sibling(*p);
      }
      stack.go_to_next_sibling();
      while(!stack.empty() && stack.current_node() == nullptr)
      {
        stack.pop_back();
        if(!stack.empty())
        {
          auto current = stack.current_node();
          INVARIANT(
            current != nullptr,
            "ranges in the stack should be positioned on existing nodes");
          // We came back to current after all its children
          strategy.parent(*current);
          if(stack.has_next_sibling())
          {
            auto p = stack.parent();
            INVARIANT(p, "siblings must have a parent");
            strategy.next_sibling(*p);
          }
          stack.go_to_next_sibling();
        }
        else
        {
          strategy.parent(ast);
        }
      }
    }
  }
}

static void print_data(std::ostream &stream, const smt2_astt &ast)
{
  if(ast.id() == ID_symbol || ast.id() == ID_constant)
  {
    INVARIANT(
      ast.read().named_sub.has_value(),
      "constant and symbols should have an non-empty `named_sub` field");
    stream << ast.read().named_sub.value();
  }
  else if(ast.id() == ID_string_constant)
  {
    stream << '\"' << ast.read().named_sub.value() << '\"';
  }
  else if(ast.id() == ID_tuple && ast.read().sub.empty())
  {
    stream << "()";
  }
}

std::ostream &operator<<(std::ostream &stream, const smt2_astt &ast)
{
  smt2_ast_strategyt print_visitor;
  print_visitor.data = [&stream](const smt2_astt &ast) {
    print_data(stream, ast);
  };
  print_visitor.first_child = [&stream](const smt2_astt &ast) {
    if(ast.id() == ID_identifier)
      stream << "(_ ";
    else if(ast.id() == ID_forall)
      stream << "(forall ";
    else if(ast.id() == ID_exists)
      stream << "(exists ";
    else if(ast.id() == ID_let)
      stream << "(let ";
    else if(ast.id() == ID_par)
      stream << "(par ";
    else
      stream << "(";
  };
  print_visitor.next_sibling = [&stream](const smt2_astt &ast) {
    stream << " ";
  };
  print_visitor.parent = [&stream](const smt2_astt &ast) { stream << ")"; };
  dfs(ast, print_visitor);
  return stream;
}

smt2_sortt::smt2_sortt(
  smt2_identifiert identifier,
  std::vector<smt2_sortt> &&parameters)
  : smt2_astt(ID_type)
{
  if(!parameters.empty())
  {
    auto &subs = write().sub;
    subs.emplace_back(std::move(identifier));
    std::move(parameters.begin(), parameters.end(), std::back_inserter(subs));
  }
  else
    *this = smt2_sortt(std::move(identifier));
}
