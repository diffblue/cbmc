/** -*- C++ -*- *****************************************************\

Module: String constraints.
        These are formulas talking about strings. We implemented two
        forms of constraints: `string_constraintt` implements formulas
        of the form $\forall univ_var \in [lb,ub[. premise => body$,
	and not_contains_constraintt implements those of the form:
        $\forall x in [lb,ub[. p(x) => \exists y in [lb,ub[.
	s1[x+y] != s2[y]$.

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint.h>
