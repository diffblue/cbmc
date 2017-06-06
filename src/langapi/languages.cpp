/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/


#include "languages.h"

languagest::languagest(const namespacet &_ns, languaget *_language):ns(_ns)
{
  language=_language;
}

languagest::~languagest()
{
  delete language;
}
