/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include "languages.h"

/*******************************************************************\

Function: languagest::languagest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

languagest::languagest(const namespacet &_ns, languaget *_language):ns(_ns)
{
  language=_language;
}

/*******************************************************************\

Function: languagest::~languagest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

languagest::~languagest()
{
  delete language;
}

