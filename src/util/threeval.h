/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_THREEVAL_H
#define CPROVER_UTIL_THREEVAL_H

#include <iosfwd>

//
// three valued logic
//

class tvt
{
public:
  // NOLINTNEXTLINE(readability/identifiers)
  enum class tv_enumt : unsigned char { TV_FALSE, TV_UNKNOWN, TV_TRUE };

  bool is_true() const { return value==tv_enumt::TV_TRUE; }
  bool is_false() const { return value==tv_enumt::TV_FALSE; }
  bool is_unknown() const { return value==tv_enumt::TV_UNKNOWN; }
  bool is_known() const
  {
    return value==tv_enumt::TV_TRUE || value==tv_enumt::TV_FALSE;
  }

  static inline tvt unknown()
  {
    return tvt(tv_enumt::TV_UNKNOWN);
  }

  const char *to_string() const;

  tv_enumt get_value() const
  {
    return value;
  }

  tvt():value(tv_enumt::TV_UNKNOWN)
  {
  }

  explicit tvt(bool b):value(b?tv_enumt::TV_TRUE:tv_enumt::TV_FALSE)
  {
  }

  explicit tvt(tv_enumt v):value(v)
  {
  }

  bool operator==(const tvt other) const
  {
    return value==other.value;
  }

  bool operator!=(const tvt other) const
  {
    return value!=other.value;
  }

  tvt operator&&(const tvt other) const
  {
    if(is_false() || other.is_false())
      return tvt(false);
    if(is_true() && other.is_true())
      return tvt(true);

    return unknown();
  }

  tvt operator||(const tvt other) const
  {
    if(is_true() || other.is_true())
      return tvt(true);
    if(is_false() && other.is_false())
      return tvt(false);

    return unknown();
  }

  tvt operator!() const
  {
    if(is_unknown())
      return unknown();
    if(is_true())
      return tvt(false);

    return tvt(true);
  }

protected:
  tv_enumt value;
};

std::ostream &operator << (std::ostream &out, const tvt &a);

#endif // CPROVER_UTIL_THREEVAL_H
