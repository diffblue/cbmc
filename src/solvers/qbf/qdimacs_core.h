/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/


#ifndef CPROVER_SOLVERS_QBF_QDIMACS_CORE_H
#define CPROVER_SOLVERS_QBF_QDIMACS_CORE_H

#include <map>

#include <util/expr.h>

#include "qdimacs_cnf.h"

class qdimacs_coret:public qdimacs_cnft
{
public:
  virtual tvt l_get(literalt a) const=0;
  virtual bool is_in_core(literalt l) const=0;

  enum modeltypet { M_TRUE, M_FALSE, M_DONTCARE, M_COMPLEX };
  virtual modeltypet m_get(literalt a) const=0;

  using symbol_mapt = std::pair<exprt, unsigned>;
  using variable_mapt = std::map<unsigned, symbol_mapt>;
  variable_mapt variable_map;  // variable -> symbol/index map
  virtual const exprt f_get(literalt v)=0;

  void simplify_extractbits(exprt &expr) const;
};

#endif // CPROVER_SOLVERS_QBF_QDIMACS_CORE_H
