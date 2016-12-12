/** -*- C++ -*- *****************************************************\

Module: String constraints
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint.h>


// string_constraintt::string_constraintt(const symbol_exprt & univ, const exprt & bound_inf, const exprt & bound_sup, const exprt &prem, const exprt &body)
//   : string_constraintt(prem,body)
// {
//   copy_to_operands(univ, bound_sup, bound_inf);
// }

// string_constraintt string_constraintt::with_exists(const symbol_exprt & exist, const exprt & bound_inf, const exprt & bound_sup)
// {
//   assert(!is_univ_quant());
//   return string_constraintt
//     (and_exprt(*this,
// 	       and_exprt(binary_relation_exprt(exist, ID_ge, bound_inf),
// 			 binary_relation_exprt(exist, ID_lt, bound_sup))));
// }

// string_constraintt string_constraintt::with_exists(const symbol_exprt & univ, const exprt & bound_sup)
// {
//   return with_exists(univ,refined_string_typet::index_zero(),bound_sup);
// }
