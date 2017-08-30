/*******************************************************************\

Module: Container for C-Strings

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Container for C-Strings

#include "dstring.h"
#include "serializer.h"


/// Serializes this instance to/from the given serializer.
/// \param serializer: The serializer to read from/write to
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
