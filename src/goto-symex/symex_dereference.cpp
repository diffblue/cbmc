/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/invariant.h>
#include <util/pointer_offset_size.h>

#include <pointer-analysis/value_set_dereference.h>

#include "expr_skeleton.h"
#include "path_storage.h"
#include "symex_assign.h"
#include "symex_dereference_state.h"

/// Transforms an lvalue expression by replacing any dereference operations it
/// contains with explicit references to the objects they may point to (using
/// \ref goto_symext::dereference_rec), and translates `byte_extract,` `member`
/// and `index` operations into integer offsets from a root symbol (if any).
/// These are ultimately expressed in the form
/// `(target_type*)((char*)(&underlying_symbol) + offset)`.
/// \param expr: expression to replace with normalised, dereference-free form
/// \param state: working state. See \ref goto_symext::dereference for possible
///   side-effects of a dereference operation.
/// \param keep_array: if true and an underlying object is an array, return
///   its address (`&array`); otherwise return the address of its first element
///   (`&array[0]).
/// \return the transformed lvalue expression
exprt goto_symext::address_arithmetic(
  const exprt &expr,
  statet &state,
  bool keep_array)
{
  exprt result;

  if(expr.id()==ID_byte_extract_little_endian ||
     expr.id()==ID_byte_extract_big_endian)
  {
    // address_of(byte_extract(op, offset, t)) is
    // address_of(op) + offset with adjustments for arrays

    const byte_extract_exprt &be=to_byte_extract_expr(expr);

    // recursive call
    result = address_arithmetic(be.op(), state, keep_array);

    if(be.op().type().id() == ID_array && result.id() == ID_address_of)
    {
      address_of_exprt &a=to_address_of_expr(result);

      // turn &a of type T[i][j] into &(a[0][0])
      for(const typet *t = &(a.type().subtype());
          t->id() == ID_array && expr.type() != *t;
          t = &(to_array_type(*t).element_type()))
        a.object() = index_exprt(a.object(), from_integer(0, c_index_type()));
    }

    // do (expr.type() *)(((char *)op)+offset)
    result=typecast_exprt(result, pointer_type(char_type()));

    // there could be further dereferencing in the offset
    exprt offset=be.offset();
    dereference_rec(offset, state, false, false);

    result=plus_exprt(result, offset);

    // treat &array as &array[0]
    const typet &expr_type = expr.type();
    typet dest_type_subtype;

    if(expr_type.id()==ID_array && !keep_array)
      dest_type_subtype = to_array_type(expr_type).element_type();
    else
      dest_type_subtype=expr_type;

    result=typecast_exprt(result, pointer_type(dest_type_subtype));
  }
  else if(expr.id()==ID_index ||
          expr.id()==ID_member)
  {
    object_descriptor_exprt ode;
    ode.build(expr, ns);

    const byte_extract_exprt be =
      make_byte_extract(ode.root_object(), ode.offset(), expr.type());

    // recursive call
    result = address_arithmetic(be, state, keep_array);

    do_simplify(result);
  }
  else if(expr.id()==ID_dereference)
  {
    // ANSI-C guarantees &*p == p no matter what p is,
    // even if it's complete garbage
    // just grab the pointer, but be wary of further dereferencing
    // in the pointer itself
    result=to_dereference_expr(expr).pointer();
    dereference_rec(result, state, false, false);
  }
  else if(expr.id()==ID_if)
  {
    if_exprt if_expr=to_if_expr(expr);

    // the condition is not an address
    dereference_rec(if_expr.cond(), state, false, false);

    // recursive call
    if_expr.true_case() =
      address_arithmetic(if_expr.true_case(), state, keep_array);
    if_expr.false_case() =
      address_arithmetic(if_expr.false_case(), state, keep_array);

    result=if_expr;
  }
  else if(expr.id()==ID_symbol ||
          expr.id()==ID_string_constant ||
          expr.id()==ID_label ||
          expr.id()==ID_array)
  {
    // give up, just dereference
    result=expr;
    dereference_rec(result, state, false, false);

    // turn &array into &array[0]
    if(result.type().id() == ID_array && !keep_array)
      result = index_exprt(result, from_integer(0, c_index_type()));

    // handle field-sensitive SSA symbol
    mp_integer offset=0;
    if(is_ssa_expr(expr))
    {
      auto offset_opt = compute_pointer_offset(expr, ns);
      PRECONDITION(offset_opt.has_value());
      offset = *offset_opt;
    }

    if(offset>0)
    {
      const byte_extract_exprt be = make_byte_extract(
        to_ssa_expr(expr).get_l1_object(),
        from_integer(offset, c_index_type()),
        expr.type());

      result = address_arithmetic(be, state, keep_array);

      do_simplify(result);
    }
    else
      result=address_of_exprt(result);
  }
  else if(expr.id() == ID_typecast)
  {
    const typecast_exprt &tc_expr = to_typecast_expr(expr);

    result = address_arithmetic(tc_expr.op(), state, keep_array);

    // treat &array as &array[0]
    const typet &expr_type = expr.type();
    typet dest_type_subtype;

    if(expr_type.id() == ID_array && !keep_array)
      dest_type_subtype = to_array_type(expr_type).element_type();
    else
      dest_type_subtype = expr_type;

    result = typecast_exprt(result, pointer_type(dest_type_subtype));
  }
  else
    throw unsupported_operation_exceptiont(
      "goto_symext::address_arithmetic does not handle " + expr.id_string());

  const typet &expr_type = expr.type();
  INVARIANT(
    (expr_type.id() == ID_array && !keep_array) ||
      pointer_type(expr_type) == result.type(),
    "either non-persistent array or pointer to result");

  return result;
}

symbol_exprt
goto_symext::cache_dereference(exprt &dereference_result, statet &state)
{
  auto const cache_key = [&] {
    auto cache_key =
      state.field_sensitivity.apply(ns, state, dereference_result, false);
    if(auto let_expr = expr_try_dynamic_cast<let_exprt>(dereference_result))
    {
      let_expr->value() = state.rename<L2>(let_expr->value(), ns).get();
    }
    else
    {
      cache_key = state.rename<L2>(cache_key, ns).get();
    }
    return cache_key;
  }();

  if(auto cached = state.dereference_cache.find(cache_key))
  {
    return *cached;
  }

  auto const &cache_symbol = get_fresh_aux_symbol(
    cache_key.type(),
    "symex",
    "dereference_cache",
    dereference_result.source_location(),
    language_mode,
    ns,
    state.symbol_table);

  // we need to lift possible lets
  // (come from the value set to avoid repeating complex pointer comparisons)
  auto cache_value = cache_key;
  lift_lets(state, cache_value);

  auto assign = symex_assignt{
    state, symex_targett::assignment_typet::STATE, ns, symex_config, target};

  auto cache_symbol_expr = cache_symbol.symbol_expr();
  assign.assign_symbol(
    to_ssa_expr(state.rename<L1>(cache_symbol_expr, ns).get()),
    expr_skeletont{},
    cache_value,
    {});

  state.dereference_cache.insert(cache_key, cache_symbol_expr);
  return cache_symbol_expr;
}

/// If \p expr is a \ref dereference_exprt, replace it with explicit references
/// to the objects it may point to. Otherwise recursively apply this function to
/// \p expr's operands, with special cases for address-of (handled by \ref
/// goto_symext::address_arithmetic) and certain common expression patterns
/// such as `&struct.flexible_array[0]` (see inline comments in code).
/// Note that \p write is used to alter behaviour when this function is
/// operating on the LHS of an assignment. Similarly \p is_in_quantifier
/// indicates when the dereference is inside a quantifier (related to scoping
/// when dereference caching is enabled).
/// For full details of this method's pointer replacement and potential side-
/// effects see \ref goto_symext::dereference
void goto_symext::dereference_rec(
  exprt &expr,
  statet &state,
  bool write,
  bool is_in_quantifier)
{
  if(expr.id()==ID_dereference)
  {
    bool expr_is_not_null = false;

    if(state.threads.size() == 1)
    {
      const irep_idt &expr_function = state.source.function_id;
      if(!expr_function.empty())
      {
        const dereference_exprt to_check =
          to_dereference_expr(get_original_name(expr));

        expr_is_not_null = path_storage.safe_pointers.at(expr_function)
                             .is_safe_dereference(to_check, state.source.pc);
      }
    }

    exprt tmp1;
    tmp1.swap(to_dereference_expr(expr).pointer());

    // first make sure there are no dereferences in there
    dereference_rec(tmp1, state, false, is_in_quantifier);

    // Depending on the nature of the pointer expression, the recursive deref
    // operation might have introduced a construct such as
    // (x == &o1 ? o1 : o2).field, in which case we should simplify to push the
    // member operator inside the if, then apply field-sensitivity to yield
    // (x == &o1 ? o1..field : o2..field). value_set_dereferencet can then
    // apply the dereference operation to each of o1..field and o2..field
    // independently, as it special-cases the ternary conditional operator.
    // There may also be index operators in tmp1 which can now be resolved to
    // constant array cell references, so we replace symbols with constants
    // first, hoping for a transformation such as
    // (x == &o1 ? o1 : o2)[idx] =>
    // (x == &o1 ? o1 : o2)[2] =>
    // (x == &o1 ? o1[[2]] : o2[[2]])
    // Note we don't L2 rename non-constant symbols at this point, because the
    // value-set works in terms of L1 names and we don't want to ask it to
    // dereference an L2 pointer, which it would not have an entry for.

    tmp1 = state.rename<L1_WITH_CONSTANT_PROPAGATION>(tmp1, ns).get();

    do_simplify(tmp1);

    if(symex_config.run_validation_checks)
    {
      // make sure simplify has not re-introduced any dereferencing that
      // had previously been cleaned away
      INVARIANT(
        !has_subexpr(tmp1, ID_dereference),
        "simplify re-introduced dereferencing");
    }

    tmp1 = state.field_sensitivity.apply(ns, state, std::move(tmp1), false);

    // we need to set up some elaborate call-backs
    symex_dereference_statet symex_dereference_state(state, ns);

    value_set_dereferencet dereference(
      ns,
      state.symbol_table,
      symex_dereference_state,
      language_mode,
      expr_is_not_null,
      log);

    // std::cout << "**** " << format(tmp1) << '\n';
    exprt tmp2 =
      dereference.dereference(tmp1, symex_config.show_points_to_sets);
    // std::cout << "**** " << format(tmp2) << '\n';


    // this may yield a new auto-object
    trigger_auto_object(tmp2, state);

    // Check various conditions for when we should try to cache the expression.
    // 1. Caching dereferences must be enabled.
    // 2. Do not cache inside LHS of writes.
    // 3. Do not cache inside quantifiers (references variables outside their
    //    scope).
    // 4. Only cache "complicated" expressions, i.e. of the form
    //     [let p = <expr> in ]
    //     (p == &something ? something : ...))
    // Otherwise we should just return it unchanged.
    if(
      symex_config.cache_dereferences && !write && !is_in_quantifier &&
      (tmp2.id() == ID_if || tmp2.id() == ID_let))
    {
      expr = cache_dereference(tmp2, state);
    }
    else
    {
      expr = std::move(tmp2);
    }
  }
  else if(
    expr.id() == ID_index && to_index_expr(expr).array().id() == ID_member &&
    to_array_type(to_index_expr(expr).array().type()).size().is_zero())
  {
    // This is an expression of the form x.a[i],
    // where a is a zero-sized array. This gets
    // re-written into *(&x.a+i)

    index_exprt index_expr=to_index_expr(expr);

    address_of_exprt address_of_expr(index_expr.array());
    address_of_expr.type()=pointer_type(expr.type());

    dereference_exprt tmp{plus_exprt{address_of_expr, index_expr.index()}};
    tmp.add_source_location()=expr.source_location();

    // recursive call
    dereference_rec(tmp, state, write, is_in_quantifier);

    expr.swap(tmp);
  }
  else if(expr.id()==ID_index &&
          to_index_expr(expr).array().type().id()==ID_pointer)
  {
    // old stuff, will go away
    UNREACHABLE;
  }
  else if(expr.id()==ID_address_of)
  {
    address_of_exprt &address_of_expr=to_address_of_expr(expr);

    exprt &object=address_of_expr.object();

    expr = address_arithmetic(
      object, state, to_pointer_type(expr.type()).base_type().id() == ID_array);
  }
  else if(expr.id()==ID_typecast)
  {
    exprt &tc_op=to_typecast_expr(expr).op();

    // turn &array into &array[0] when casting to pointer-to-element-type
    if(
      tc_op.id() == ID_address_of &&
      to_address_of_expr(tc_op).object().type().id() == ID_array &&
      expr.type() ==
        pointer_type(to_address_of_expr(tc_op).object().type().subtype()))
    {
      expr = address_of_exprt(index_exprt(
        to_address_of_expr(tc_op).object(), from_integer(0, c_index_type())));

      dereference_rec(expr, state, write, is_in_quantifier);
    }
    else
    {
      dereference_rec(tc_op, state, write, is_in_quantifier);
    }
  }
  else
  {
    bool is_quantifier = expr.id() == ID_forall || expr.id() == ID_exists;
    Forall_operands(it, expr)
      dereference_rec(*it, state, write, is_in_quantifier || is_quantifier);
  }
}

static exprt
apply_to_objects_in_dereference(exprt e, const std::function<exprt(exprt)> &f)
{
  if(auto deref = expr_try_dynamic_cast<dereference_exprt>(e))
  {
    deref->op() = f(std::move(deref->op()));
    return *deref;
  }

  for(auto &sub : e.operands())
    sub = apply_to_objects_in_dereference(std::move(sub), f);
  return e;
}

/// Replace all dereference operations within \p expr with explicit references
/// to the objects they may refer to. For example, the expression `*p1 + *p2`
/// might be rewritten to `obj1 + (p2 == &obj2 ? obj2 : obj3)` in the case where
/// `p1` is known to point to `obj1` and `p2` points to either `obj2` or `obj3`.
/// The expression, and any object references introduced, are renamed to L1 in
/// the process (so in fact we would get `obj1!0@3 + (p2!0@1 == ....` rather
/// than the exact example given above).
///
/// It may have two kinds of side-effect:
///
/// 1. When an expression may (or must) point to something which cannot legally
///    be dereferenced, such as a null pointer or an integer cast to a pointer,
///    a "failed object" is created instead, via one of two routes:
///
///    a. if the `add_failed_symbols` pass has been run then a pointer-typed
///       symbol `x` will have a corresponding failed symbol `x$object`. This
///       is replicated according to L1 renaming on demand, so for example on
///       the first failed dereference of `x!5@10` we will create
///       `x$object!5@10` and add that to the symbol table.
///       This addition is made by
///       \ref symex_dereference_statet::get_or_create_failed_symbol
///
///    b. if such a failed symbol can't be found then symex will create one of
///       its own, called `symex::failed_symbol` with some suffix. This is done
///       by \ref value_set_dereferencet::dereference
///
///    In either case any newly-created symbol is added to \p state's symbol
///    table and \p expr is altered to refer to it. Typically when \p expr has
///    some legal targets as well this results in an expression like
///    `ptr == &real_obj ? real_obj : ptr$object`.
///
/// 2. Any object whose base-name ends with `auto_object` is automatically
///    initialised when dereferenced for the first time, creating a tree of
///    pointers leading to fresh objects each time such a pointer is
///    dereferenced. If new objects are created by this mechanism then
///    state will be altered (by `symex_assign`) to initialise them.
///    See \ref auto_objects.cpp for details.
void goto_symext::dereference(exprt &expr, statet &state, bool write)
{
  PRECONDITION(!state.call_stack().empty());

  // Symbols whose address is taken need to be renamed to level 1
  // in order to distinguish addresses of local variables
  // from different frames.
  expr = apply_to_objects_in_dereference(std::move(expr), [&](exprt e) {
    return state.field_sensitivity.apply(
      ns, state, state.rename<L1>(std::move(e), ns).get(), false);
  });

  // start the recursion!
  dereference_rec(expr, state, write, false);
  // dereferencing may introduce new symbol_exprt
  // (like __CPROVER_memory)
  expr = state.rename<L1>(std::move(expr), ns).get();

  // Dereferencing is likely to introduce new member-of-if constructs --
  // for example, "x->field" may have become "(x == &o1 ? o1 : o2).field."
  // Run expression simplification, which converts that to
  // (x == &o1 ? o1.field : o2.field))
  // before applying field sensitivity. Field sensitivity can then turn such
  // field-of-symbol expressions into atomic SSA expressions instead of having
  // to rewrite all of 'o1' otherwise.
  // Even without field sensitivity this can be beneficial: for example,
  // "(b ? s1 : s2).member := X" results in
  // (b ? s1 : s2) := (b ? s1 : s2) with (member := X)
  // and then
  // s1 := b ? ((b ? s1 : s2) with (member := X)) : s1
  // when all we need is
  // s1 := s1 with (member := X) [and guard b]
  // s2 := s2 with (member := X) [and guard !b]
  do_simplify(expr);

  if(symex_config.run_validation_checks)
  {
    // make sure simplify has not re-introduced any dereferencing that
    // had previously been cleaned away
    INVARIANT(
      !has_subexpr(expr, ID_dereference),
      "simplify re-introduced dereferencing");
  }

  expr = state.field_sensitivity.apply(ns, state, std::move(expr), write);
}
