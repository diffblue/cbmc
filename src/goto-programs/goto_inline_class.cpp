/*******************************************************************\

Module: Function Inlining

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Function Inlining

#include "goto_inline_class.h"

#ifdef DEBUG
#include <iostream>
#endif

#include <util/base_type.h>
#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/invariant.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/std_expr.h>

#include <langapi/language_util.h>

#include "remove_skip.h"
#include "goto_inline.h"

void goto_inlinet::parameter_assignments(
  const goto_programt::targett target,
  const irep_idt &function_name, // name of called function
  const code_typet &code_type, // type of called function
  const exprt::operandst &arguments, // arguments of call
  goto_programt &dest)
{
  PRECONDITION(target->is_function_call());
  PRECONDITION(dest.empty());

  const source_locationt &source_location=target->source_location;

  // iterates over the operands
  exprt::operandst::const_iterator it1=arguments.begin();

  const code_typet::parameterst &parameter_types=
    code_type.parameters();

  // iterates over the types of the parameters
  for(const auto &parameter : parameter_types)
  {
    // this is the type the n-th argument should be
    const typet &par_type=ns.follow(parameter.type());

    const irep_idt &identifier=parameter.get_identifier();

    DATA_INVARIANT(
      !identifier.empty(),
      source_location.as_string() + ": no identifier for function parameter");

    {
      const symbolt &symbol=ns.lookup(identifier);

      goto_programt::targett decl=dest.add_instruction();
      decl->make_decl();
      decl->code=code_declt(symbol.symbol_expr());
      decl->code.add_source_location()=source_location;
      decl->source_location=source_location;
      decl->function=adjust_function?target->function:function_name;
    }

    // this is the actual parameter
    exprt actual;

    // if you run out of actual arguments there was a mismatch
    if(it1==arguments.end())
    {
      warning().source_location=source_location;
      warning() << "call to `" << function_name << "': "
                << "not enough arguments, "
                << "inserting non-deterministic value" << eom;

      actual = side_effect_expr_nondett(par_type, source_location);
    }
    else
      actual=*it1;

    // nil means "don't assign"
    if(actual.is_nil())
    {
    }
    else
    {
      // it should be the same exact type as the parameter,
      // subject to some exceptions
      if(!base_type_eq(par_type, actual.type(), ns))
      {
        const typet &f_partype=ns.follow(par_type);
        const typet &f_acttype=ns.follow(actual.type());

        // we are willing to do some conversion
        if((f_partype.id()==ID_pointer &&
            f_acttype.id()==ID_pointer) ||
           (f_partype.id()==ID_pointer &&
            f_acttype.id()==ID_array &&
            f_partype.subtype()==f_acttype.subtype()))
        {
          actual.make_typecast(par_type);
        }
        else if((f_partype.id()==ID_signedbv ||
                 f_partype.id()==ID_unsignedbv ||
                 f_partype.id()==ID_bool) &&
                (f_acttype.id()==ID_signedbv ||
                 f_acttype.id()==ID_unsignedbv ||
                 f_acttype.id()==ID_bool))
        {
          actual.make_typecast(par_type);
        }
        else
        {
          UNREACHABLE;
        }
      }

      // adds an assignment of the actual parameter to the formal parameter
      code_assignt assignment(symbol_exprt(identifier, par_type), actual);
      assignment.add_source_location()=source_location;

      dest.add_instruction(ASSIGN);
      dest.instructions.back().source_location=source_location;
      dest.instructions.back().code.swap(assignment);
      dest.instructions.back().function=
        adjust_function?target->function:function_name;
    }

    if(it1!=arguments.end())
      ++it1;
  }

  if(it1!=arguments.end())
  {
    // too many arguments -- we just ignore that, no harm done
  }
}

void goto_inlinet::parameter_destruction(
  const goto_programt::targett target,
  const irep_idt &function_name, // name of called function
  const code_typet &code_type, // type of called function
  goto_programt &dest)
{
  PRECONDITION(target->is_function_call());
  PRECONDITION(dest.empty());

  const source_locationt &source_location=target->source_location;

  const code_typet::parameterst &parameter_types=
    code_type.parameters();

  // iterates over the types of the parameters
  for(const auto &parameter : parameter_types)
  {
    const irep_idt &identifier=parameter.get_identifier();

    INVARIANT(
      !identifier.empty(),
      source_location.as_string() + ": no identifier for function parameter");

    {
      const symbolt &symbol=ns.lookup(identifier);

      goto_programt::targett dead=dest.add_instruction();
      dead->make_dead();
      dead->code=code_deadt(symbol.symbol_expr());
      dead->code.add_source_location()=source_location;
      dead->source_location=source_location;
      dead->function=adjust_function?target->function:function_name;
    }
  }
}

void goto_inlinet::replace_return(
  goto_programt &dest, // inlining this
  const exprt &lhs) // lhs in caller
{
  for(goto_programt::instructionst::iterator
      it=dest.instructions.begin();
      it!=dest.instructions.end();
      it++)
  {
    if(it->is_return())
    {
      if(lhs.is_not_nil())
      {
        if(it->code.operands().size()!=1)
        {
          warning().source_location=it->code.find_source_location();
          warning() << "return expects one operand!\n"
                    << it->code.pretty() << eom;
          continue;
        }

        code_assignt code_assign(lhs, it->code.op0());

        // this may happen if the declared return type at the call site
        // differs from the defined return type
        if(code_assign.lhs().type()!=
           code_assign.rhs().type())
          code_assign.rhs().make_typecast(code_assign.lhs().type());

        it->code=code_assign;
        it->type=ASSIGN;

        it++;
      }
      else if(!it->code.operands().empty())
      {
        it->code=code_expressiont(it->code.op0());
        it->type=OTHER;
        it++;
      }
    }
  }
}

void replace_location(
  source_locationt &dest,
  const source_locationt &new_location)
{
  // we copy, and then adjust for property_id, property_class
  // and comment, if necessary

  irep_idt comment=dest.get_comment();
  irep_idt property_class=dest.get_property_class();
  irep_idt property_id=dest.get_property_id();

  dest=new_location;

  if(!comment.empty())
    dest.set_comment(comment);

  if(!property_class.empty())
    dest.set_property_class(property_class);

  if(!property_id.empty())
    dest.set_property_id(property_id);
}

void replace_location(
  exprt &dest,
  const source_locationt &new_location)
{
  Forall_operands(it, dest)
    replace_location(*it, new_location);

  if(dest.find(ID_C_source_location).is_not_nil())
    replace_location(dest.add_source_location(), new_location);
}

void goto_inlinet::insert_function_body(
  const goto_functiont &goto_function,
  goto_programt &dest,
  goto_programt::targett target,
  const exprt &lhs,
  const symbol_exprt &function,
  const exprt::operandst &arguments)
{
  PRECONDITION(target->is_function_call());
  PRECONDITION(!dest.empty());
  PRECONDITION(goto_function.body_available());

  const irep_idt identifier=function.get_identifier();

  goto_programt body;
  body.copy_from(goto_function.body);
  inline_log.copy_from(goto_function.body, body);

  goto_programt::instructiont &end=body.instructions.back();
  DATA_INVARIANT(
    end.is_end_function(),
    "final instruction of a function must be an END_FUNCTION");
  end.type=LOCATION;

  if(adjust_function)
    for(auto &instruction : body.instructions)
      instruction.function=target->function;

  // make sure the inlined function does not introduce hiding
  if(goto_function.is_hidden())
  {
    for(auto &instruction : body.instructions)
      instruction.labels.remove(CPROVER_PREFIX "HIDE");
  }

  replace_return(body, lhs);

  goto_programt tmp1;
  parameter_assignments(
    target,
    identifier,
    goto_function.type,
    arguments,
    tmp1);

  goto_programt tmp2;
  parameter_destruction(target, identifier, goto_function.type, tmp2);

  goto_programt tmp;
  tmp.destructive_append(tmp1); // par assignment
  tmp.destructive_append(body); // body
  tmp.destructive_append(tmp2); // par destruction

  goto_programt::const_targett t_it;
  t_it=goto_function.body.instructions.begin();
  unsigned begin_location_number=t_it->location_number;
  t_it=--goto_function.body.instructions.end();
  DATA_INVARIANT(
    t_it->is_end_function(),
    "final instruction of a function must be an END_FUNCTION");
  unsigned end_location_number=t_it->location_number;

  unsigned call_location_number=target->location_number;

  inline_log.add_segment(
    tmp,
    begin_location_number,
    end_location_number,
    call_location_number,
    identifier);

#if 0
  if(goto_function.is_hidden())
  {
    source_locationt new_source_location=
      function.find_source_location();

    if(new_source_location.is_not_nil())
    {
      new_source_location.set_hide();

      Forall_goto_program_instructions(it, tmp)
      {
        if(it->function==identifier)
        {
          // don't hide assignment to lhs
          if(it->is_assign() && to_code_assign(it->code).lhs()==lhs)
          {
          }
          else
          {
            replace_location(it->source_location, new_source_location);
            replace_location(it->guard, new_source_location);
            replace_location(it->code, new_source_location);
          }

          it->function=target->function;
        }
      }
    }
  }
#endif

  // kill call
  target->type=LOCATION;
  target->code.clear();
  target++;

  dest.destructive_insert(target, tmp);
}

void goto_inlinet::expand_function_call(
  goto_programt &dest,
  const inline_mapt &inline_map,
  const bool transitive,
  const bool force_full,
  goto_programt::targett target)
{
  PRECONDITION(target->is_function_call());
  PRECONDITION(!dest.empty());
  PRECONDITION(!transitive || inline_map.empty());

#ifdef DEBUG
  std::cout << "Expanding call:\n";
  dest.output_instruction(ns, "", std::cout, *target);
#endif

  exprt lhs;
  exprt function_expr;
  exprt::operandst arguments;

  get_call(target, lhs, function_expr, arguments);

  if(function_expr.id()!=ID_symbol)
    return;

  const symbol_exprt &function=to_symbol_expr(function_expr);

  const irep_idt identifier=function.get_identifier();

  if(is_ignored(identifier))
    return;

  // see if we are already expanding it
  if(recursion_set.find(identifier)!=recursion_set.end())
  {
    // it's recursive.
    // Uh. Buh. Give up.
    warning().source_location=function.find_source_location();
    warning() << "recursion is ignored on call to `" << identifier << "'"
              << eom;

    if(force_full)
      target->make_skip();

    return;
  }

  goto_functionst::function_mapt::iterator f_it=
    goto_functions.function_map.find(identifier);

  if(f_it==goto_functions.function_map.end())
  {
    warning().source_location=function.find_source_location();
    warning() << "missing function `" << identifier << "' is ignored" << eom;

    if(force_full)
      target->make_skip();

    return;
  }

  // function to inline
  goto_functiont &goto_function=f_it->second;

  if(goto_function.body_available())
  {
    if(transitive)
    {
      const goto_functiont &cached=
        goto_inline_transitive(
          identifier,
          goto_function,
          force_full);

      // insert 'cached' into 'dest' at 'target'
      insert_function_body(
        cached,
        dest,
        target,
        lhs,
        function,
        arguments);

      progress() << "Inserting " << identifier << " into caller" << eom;
      progress() << "Number of instructions: "
                 << cached.body.instructions.size() << eom;

      if(!caching)
      {
        progress() << "Removing " << identifier << " from cache" << eom;
        progress() << "Number of instructions: "
                   << cached.body.instructions.size() << eom;

        inline_log.cleanup(cached.body);
        cache.erase(identifier);
      }
    }
    else
    {
      // inline non-transitively
      goto_inline_nontransitive(
        identifier,
        goto_function,
        inline_map,
        force_full);

      // insert 'goto_function' into 'dest' at 'target'
      insert_function_body(
        goto_function,
        dest,
        target,
        lhs,
        function,
        arguments);
    }
  }
  else // no body available
  {
    if(no_body_set.insert(identifier).second) // newly inserted
    {
      warning().source_location = function.find_source_location();
      warning() << "no body for function `" << identifier << "'" << eom;
    }
  }
}

void goto_inlinet::get_call(
  goto_programt::const_targett it,
  exprt &lhs,
  exprt &function,
  exprt::operandst &arguments)
{
  PRECONDITION(it->is_function_call());

  const code_function_callt &call=to_code_function_call(it->code);

  lhs=call.lhs();
  function=call.function();
  arguments=call.arguments();
}

void goto_inlinet::goto_inline(
  const inline_mapt &inline_map,
  const bool force_full)
{
  PRECONDITION(check_inline_map(inline_map));

  Forall_goto_functions(f_it, goto_functions)
  {
    const irep_idt identifier=f_it->first;
    DATA_INVARIANT(!identifier.empty(), "function name must not be empty");
    goto_functiont &goto_function=f_it->second;

    if(!goto_function.body_available())
      continue;

    goto_inline(identifier, goto_function, inline_map, force_full);
  }
}

void goto_inlinet::goto_inline(
  const irep_idt identifier,
  goto_functiont &goto_function,
  const inline_mapt &inline_map,
  const bool force_full)
{
  recursion_set.clear();

  goto_inline_nontransitive(
    identifier,
    goto_function,
    inline_map,
    force_full);
}

void goto_inlinet::goto_inline_nontransitive(
  const irep_idt identifier,
  goto_functiont &goto_function,
  const inline_mapt &inline_map,
  const bool force_full)
{
  PRECONDITION(goto_function.body_available());

  finished_sett::const_iterator f_it=finished_set.find(identifier);

  if(f_it!=finished_set.end())
    return;

  PRECONDITION(check_inline_map(identifier, inline_map));

  goto_programt &goto_program=goto_function.body;

  const inline_mapt::const_iterator im_it=inline_map.find(identifier);

  if(im_it==inline_map.end())
    return;

  const call_listt &call_list=im_it->second;

  if(call_list.empty())
    return;

  recursion_set.insert(identifier);

  for(const auto &call : call_list)
  {
    const bool transitive=call.second;

    const inline_mapt &new_inline_map=
      transitive?inline_mapt():inline_map;

    expand_function_call(
      goto_program,
      new_inline_map,
      transitive,
      force_full,
      call.first);
  }

  recursion_set.erase(identifier);

  // remove_skip(goto_program);
  // goto_program.update(); // does not change loop ids

  finished_set.insert(identifier);
}

const goto_inlinet::goto_functiont &goto_inlinet::goto_inline_transitive(
  const irep_idt identifier,
  const goto_functiont &goto_function,
  const bool force_full)
{
  PRECONDITION(goto_function.body_available());

  cachet::const_iterator c_it=cache.find(identifier);

  if(c_it!=cache.end())
  {
    const goto_functiont &cached=c_it->second;
    DATA_INVARIANT(
      cached.body_available(),
      "body of cached functions must be available");
    return cached;
  }

  goto_functiont &cached=cache[identifier];
  DATA_INVARIANT(
    cached.body.empty(), "body of new function in cache must be empty");

  progress() << "Creating copy of " << identifier << eom;
  progress() << "Number of instructions: "
             << goto_function.body.instructions.size() << eom;

  cached.copy_from(goto_function); // location numbers not changed
  inline_log.copy_from(goto_function.body, cached.body);

  goto_programt &goto_program=cached.body;

  goto_programt::targetst call_list;

  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_function_call())
      call_list.push_back(i_it);
  }

  if(call_list.empty())
    return cached;

  recursion_set.insert(identifier);

  for(const auto &call : call_list)
  {
    expand_function_call(
      goto_program,
      inline_mapt(),
      true,
      force_full,
      call);
  }

  recursion_set.erase(identifier);

  // remove_skip(goto_program);
  // goto_program.update(); // does not change loop ids

  return cached;
}

bool goto_inlinet::is_ignored(const irep_idt id) const
{
  return id == CPROVER_PREFIX "cleanup" || id == CPROVER_PREFIX "set_must" ||
         id == CPROVER_PREFIX "set_may" || id == CPROVER_PREFIX "clear_must" ||
         id == CPROVER_PREFIX "clear_may" || id == CPROVER_PREFIX "cover";
}

bool goto_inlinet::check_inline_map(
  const irep_idt identifier,
  const inline_mapt &inline_map) const
{
  goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(identifier);

  PRECONDITION(f_it != goto_functions.function_map.end());

  inline_mapt::const_iterator im_it=inline_map.find(identifier);

  if(im_it==inline_map.end())
    return true;

  const call_listt &call_list=im_it->second;

  if(call_list.empty())
    return true;

  unsigned ln = goto_programt::instructiont::nil_target;

  for(const auto &call : call_list)
  {
    const goto_programt::const_targett target=call.first;

    #if 0
    // might not hold if call was previously inlined
    if(target->function!=identifier)
      return false;
    #endif

    // location numbers increasing
    if(
      ln != goto_programt::instructiont::nil_target &&
      target->location_number <= ln)
    {
      return false;
    }

    if(!target->is_function_call())
      return false;

    ln=target->location_number;
  }

  return true;
}

bool goto_inlinet::check_inline_map(const inline_mapt &inline_map) const
{
  forall_goto_functions(f_it, goto_functions)
  {
    if(!check_inline_map(f_it->first, inline_map))
      return false;
  }

  return true;
}

void goto_inlinet::output_inline_map(
  std::ostream &out,
  const inline_mapt &inline_map)
{
  PRECONDITION(check_inline_map(inline_map));

  for(const auto &it : inline_map)
  {
    const irep_idt &id=it.first;
    const call_listt &call_list=it.second;

    out << "Function: " << id << "\n";

    goto_functionst::function_mapt::const_iterator f_it=
      goto_functions.function_map.find(id);

    std::string call="-";

    if(f_it!=goto_functions.function_map.end() &&
       !call_list.empty())
    {
      const goto_functiont &goto_function=f_it->second;
      DATA_INVARIANT(
        goto_function.body_available(),
        "cannot inline function with empty body");

      const goto_programt &goto_program=goto_function.body;

      for(const auto &call : call_list)
      {
        const goto_programt::const_targett target=call.first;
        bool transitive=call.second;

        out << "  Call:\n";
        goto_program.output_instruction(ns, "", out, *target);
        out << "  Transitive: " << transitive << "\n";
      }
    }
    else
    {
      out << "  -\n";
    }
  }
}

void goto_inlinet::output_cache(std::ostream &out) const
{
  for(auto it=cache.begin(); it!=cache.end(); it++)
  {
    if(it!=cache.begin())
      out << ", ";

    out << it->first << "\n";
  }
}

// remove segment that refer to the given goto program
void goto_inlinet::goto_inline_logt::cleanup(
  const goto_programt &goto_program)
{
  forall_goto_program_instructions(it, goto_program)
    log_map.erase(it);
}

void goto_inlinet::goto_inline_logt::cleanup(
  const goto_functionst::function_mapt &function_map)
{
  for(const auto &it : function_map)
  {
    const goto_functiont &goto_function=it.second;

    if(!goto_function.body_available())
      continue;

    cleanup(goto_function.body);
  }
}

void goto_inlinet::goto_inline_logt::add_segment(
  const goto_programt &goto_program,
  const unsigned begin_location_number,
  const unsigned end_location_number,
  const unsigned call_location_number,
  const irep_idt function)
{
  PRECONDITION(!goto_program.empty());
  PRECONDITION(!function.empty());
  PRECONDITION(end_location_number >= begin_location_number);

  goto_programt::const_targett start=goto_program.instructions.begin();
  INVARIANT(
    log_map.find(start) == log_map.end(),
    "inline function should be registered once in map of inline functions");

  goto_programt::const_targett end=goto_program.instructions.end();
  end--;

  goto_inline_log_infot info;
  info.begin_location_number=begin_location_number;
  info.end_location_number=end_location_number;
  info.call_location_number=call_location_number;
  info.function=function;
  info.end=end;

  log_map[start]=info;
}

void goto_inlinet::goto_inline_logt::copy_from(
  const goto_programt &from,
  const goto_programt &to)
{
  PRECONDITION(from.instructions.size() == to.instructions.size());

  goto_programt::const_targett it1=from.instructions.begin();
  goto_programt::const_targett it2=to.instructions.begin();

  for(; it1!=from.instructions.end(); it1++, it2++)
  {
    DATA_INVARIANT(
      it2 != to.instructions.end(),
      "'to' target function is not allowed to be empty");
    DATA_INVARIANT(
      it1->location_number == it2->location_number,
      "both functions' instruction should point to the same source");

    log_mapt::const_iterator l_it=log_map.find(it1);
    if(l_it!=log_map.end()) // a segment starts here
    {
      // as 'to' is a fresh copy
      DATA_INVARIANT(
        log_map.find(it2) == log_map.end(),
        "'to' target is not expected to be in the log_map");

      goto_inline_log_infot info=l_it->second;
      goto_programt::const_targett end=info.end;

      // find end of new
      goto_programt::const_targett tmp_it=it1;
      goto_programt::const_targett new_end=it2;
      while(tmp_it!=end)
      {
        new_end++;
        tmp_it++;
      }

      info.end=new_end;

      log_map[it2]=info;
    }
  }
}

// call after goto_functions.update()!
jsont goto_inlinet::goto_inline_logt::output_inline_log_json() const
{
  json_objectt json_result;
  json_arrayt &json_inlined=json_result["inlined"].make_array();

  for(const auto &it : log_map)
  {
    json_objectt &object=json_inlined.push_back().make_object();

    goto_programt::const_targett start=it.first;
    const goto_inline_log_infot &info=it.second;
    goto_programt::const_targett end=info.end;

    PRECONDITION(start->location_number <= end->location_number);

    object["call"]=json_numbert(std::to_string(info.call_location_number));
    object["function"]=json_stringt(info.function.c_str());

    json_arrayt &json_orig=object["originalSegment"].make_array();
    json_orig.push_back()=json_numbert(std::to_string(
      info.begin_location_number));
    json_orig.push_back()=json_numbert(std::to_string(
      info.end_location_number));

    json_arrayt &json_new=object["inlinedSegment"].make_array();
    json_new.push_back()=json_numbert(std::to_string(start->location_number));
    json_new.push_back()=json_numbert(std::to_string(end->location_number));
  }

  return std::move(json_result);
}
