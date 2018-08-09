/*******************************************************************\

Module: Expand pointer predicates in assertions/assumptions.

Author: Klaas Pruiksma

Date: June 2018

\*******************************************************************/

/// \file
/// Replace pointer predicates (e.g. __CPROVER_points_to_valid_memory)
/// in assumptions and assertions with suitable expressions and additional
/// instructions.

#include "expand_pointer_predicates.h"

#include <analyses/local_bitvector_analysis.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/pointer_predicates.h>
#include <util/simplify_expr.h>

#include <goto-programs/goto_model.h>

class expand_pointer_predicatest
{
public:
  expand_pointer_predicatest(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions):
      ns(_symbol_table),
      symbol_table(_symbol_table),
      goto_functions(_goto_functions),
      local_bitvector_analysis(nullptr)
  {
  }

  void operator()();

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  local_bitvector_analysist *local_bitvector_analysis;

  void expand_pointer_predicates();

  void expand_assumption(
    goto_programt &program,
    goto_programt::targett target,
    exprt &assume_expr);

  void expand_assertion(exprt &assert_expr);

  const symbolt &new_tmp_symbol(
    const typet &type,
    const source_locationt &source_location);
};

bool is_lvalue(const exprt &expr);

void expand_pointer_predicatest::expand_pointer_predicates()
{
  Forall_goto_functions(f_it, goto_functions)
  {
    goto_functionst::goto_functiont &goto_function = f_it->second;
    local_bitvector_analysist local_bitvector_analysis_obj(goto_function);
    local_bitvector_analysis = &local_bitvector_analysis_obj;
    Forall_goto_program_instructions(i_it, goto_function.body)
    {
      if(i_it->is_assert())
      {
        expand_assertion(i_it->guard);
      }
      else if(i_it->is_assume())
      {
        expand_assumption(
          goto_function.body,
          i_it,
          i_it->guard);
          local_bitvector_analysis_obj =
            local_bitvector_analysist(goto_function);
          local_bitvector_analysis = &local_bitvector_analysis_obj;
      }
      else
      {
        continue;
      }
    }
  }
}

void expand_pointer_predicatest::expand_assumption(
  goto_programt &program,
  goto_programt::targett target,
  exprt &assume_expr)
{
  goto_programt assume_code;
  for(depth_iteratort it=assume_expr.depth_begin();
      it != assume_expr.depth_end();)
  {
    if(it->id() == ID_points_to_valid_memory)
    {
      exprt &valid_memory_expr = it.mutate();
      exprt &pointer_expr = valid_memory_expr.op0();
      exprt size_expr = valid_memory_expr.op1();
      simplify(size_expr, ns);

      // This should be forced by typechecking.
      INVARIANT(pointer_expr.type().id() == ID_pointer &&
                  is_lvalue(pointer_expr),
                "Invalid argument to valid_pointer.");

      local_bitvector_analysist::flagst flags =
        local_bitvector_analysis->get(target, pointer_expr);
      // Only create a new object if the pointer may be uninitialized.
      if(flags.is_uninitialized() || flags.is_unknown())
      {
        typet object_type = type_from_size(size_expr, ns);

        // Decl a new variable (which is therefore unconstrained)
        goto_programt::targett d = assume_code.add_instruction(DECL);
        d->function = target->function;
        d->source_location = assume_expr.source_location();
        const symbol_exprt obj =
          new_tmp_symbol(object_type, d->source_location).symbol_expr();
        d->code=code_declt(obj);

        exprt rhs;
        if(object_type.id() == ID_array)
        {
          rhs = typecast_exprt(
            address_of_exprt(
              index_exprt(obj, from_integer(0, index_type()))),
            pointer_expr.type());
        }
        else
        {
          rhs = address_of_exprt(obj);
        }

        // Point the relevant pointer to the new object
        goto_programt::targett a = assume_code.add_instruction(ASSIGN);
        a->function = target->function;
        a->source_location = assume_expr.source_location();
        a->code = code_assignt(pointer_expr, rhs);
        a->code.add_source_location() = assume_expr.source_location();
      }

      // Because some uses of this occur before deallocated, dead, and malloc
      // objects are initialized, we need to make some additional assumptions
      // to clarify that our newly allocated object is not dead, deallocated,
      // or outside the bounds of a malloc region.

      exprt check_expr =
        points_to_valid_memory_def(pointer_expr, size_expr, ns);
      valid_memory_expr.swap(check_expr);
      it.next_sibling_or_parent();
    }
    else {
      ++it;
    }
  }

  program.destructive_insert(target, assume_code);
}

void expand_pointer_predicatest::expand_assertion(exprt &assert_expr)
{
  for(depth_iteratort it = assert_expr.depth_begin();
      it != assert_expr.depth_end();)
  {
    if(it->id() == ID_points_to_valid_memory)
    {
      // Build an expression that checks validity.
      exprt &valid_memory_expr = it.mutate();
      exprt &pointer_expr = valid_memory_expr.op0();
      exprt &size_expr = valid_memory_expr.op1();

      exprt check_expr =
        points_to_valid_memory_def(pointer_expr, size_expr, ns);
      valid_memory_expr.swap(check_expr);
      it.next_sibling_or_parent();
    }
    else
    {
      ++it;
    }
  }
}

const symbolt &expand_pointer_predicatest::new_tmp_symbol(
  const typet &type,
  const source_locationt &source_location)
{
  return get_fresh_aux_symbol(
    type,
    id2string(source_location.get_function()),
    "tmp_epp",
    source_location,
    ID_C,
    symbol_table);
}

void expand_pointer_predicatest::operator()()
{
  expand_pointer_predicates();
}

void expand_pointer_predicates(goto_modelt &goto_model)
{
  expand_pointer_predicatest(goto_model.symbol_table,
                             goto_model.goto_functions)();
}
