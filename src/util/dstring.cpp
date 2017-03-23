/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "dstring.h"
#include "serializer.h"


/*******************************************************************\

  Function: dstring::serialize

  Inputs:
    serializer: The serializer to read from/write to

  Outputs:

  Purpose:
    Serializes this instance to/from the given serializer.

\*******************************************************************/
void dstringt::serialize(serializert &serializer)
{
  if(serializer.is_for_reading())
  {
    std::string str;
    serializer.serialize("dstring", str);
    no=string_container[str];
  }
  else
  {
    std::string str=as_string();
    serializer.serialize("dstring", str);
  }
}
