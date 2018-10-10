/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

// The body of value_set_domaint<VST>::transform, included from
// value_set_domain.h but retained in this out-of-line file to ease
// git merges:

template<class VST>
void value_set_domain_templatet<VST>::transform(
  const namespacet &ns,
  const irep_idt &function_from,
  locationt from_l,
  const irep_idt &function_to,
  locationt to_l)
{
  switch(from_l->type)
  {
  case GOTO:
    // ignore for now
    break;

  case END_FUNCTION:
  {
    value_set.do_end_function(
      static_analysis_baset::get_return_lhs(to_l), ns);
    break;
  }

  // Note intentional fall-through here:
  case RETURN:
  case OTHER:
  case ASSIGN:
  case DECL:
  case DEAD:
    value_set.apply_code(from_l->code, ns);
    break;

  case ASSUME:
    value_set.guard(from_l->guard, ns);
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code=
        to_code_function_call(from_l->code);

      value_set.do_function_call(
        function_to, code.arguments(), ns);
    }
    break;

  default:
    {
      // do nothing
    }
  }
}
