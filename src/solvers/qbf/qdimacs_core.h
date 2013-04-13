/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_QDIMACS_CORE_H
#define CPROVER_QDIMACS_CORE_H

#include <util/expr.h>

#include "qdimacs_cnf.h"

class qdimacs_coret:public qdimacs_cnft
{
public:
  virtual tvt l_get(literalt a) const=0;
  virtual bool is_in_core(literalt l) const=0;

  typedef enum { M_TRUE, M_FALSE, M_DONTCARE, M_COMPLEX } modeltypet;
  virtual modeltypet m_get(literalt a) const=0;

  typedef std::pair<exprt, unsigned> symbol_mapt;
  typedef std::map<unsigned, symbol_mapt> variable_mapt;
  variable_mapt variable_map;  // variable -> symbol/index map
  virtual const exprt f_get(literalt v)=0;

  void simplify_extractbits(exprt &expr) const;
};

#endif /*CPROVER_QDIMACS_CORE_H*/
