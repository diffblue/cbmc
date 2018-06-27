/*******************************************************************\

 Module: String solver

 Author: Diffblue Ltd.

\*******************************************************************/

#include "string_constraint.h"

string_constraintt::string_constraintt(
  symbol_exprt _univ_var,
  exprt lower_bound,
  exprt upper_bound,
  exprt body)
  : univ_var(_univ_var),
    lower_bound(lower_bound),
    upper_bound(upper_bound),
    body(body)
{
}
