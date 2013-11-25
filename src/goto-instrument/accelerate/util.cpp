#include <util/std_types.h>

#include "util.h"

/**
 * Convenience function -- is the type a bitvector of some kind?
 */
bool is_bitvector(const typet &t) {
  return t.id() == ID_bv ||
         t.id() == ID_signedbv ||
         t.id() == ID_unsignedbv;
}

/**
 * Convenience function -- is the type signed?
 */
bool is_signed(const typet &t) {
  return t.id() == ID_signedbv;
}


/**
 * Conveniece function -- is the type unsigned?
 */
bool is_unsigned(const typet &t) {
  return t.id() == ID_bv ||
         t.id() == ID_unsignedbv;
}

/**
 * Return the smallest type that both t1 and t2 can be cast to without losing
 * information.
 *
 * e.g.
 *
 * join_types(unsignedbv_typet(32), unsignedbv_typet(16)) = unsignedbv_typet(32)
 * join_types(signedbv_typet(16), unsignedbv_typet(16)) = signedbv_typet(17)
 * join_types(signedbv_typet(32), signedbv_typet(32)) = signedbv_typet(32)
 */
typet join_types(const typet &t1, const typet &t2) {
  // Handle the simple case first...
  if (t1 == t2) {
    return t1;
  }

  // OK, they're not the same type.  Are they both bitvectors?
  if (is_bitvector(t1) && is_bitvector(t2)) {
    // They are.  That makes things easy!  There are three cases to consider:
    // both types are unsigned, both types are signed or there's one of each.

    bitvector_typet b1 = to_bitvector_type(t1);
    bitvector_typet b2 = to_bitvector_type(t2);

    if (is_unsigned(b1) && is_unsigned(b2)) {
      // We just need to take the max of their widths.
      unsigned int width = std::max(b1.get_width(), b2.get_width());
      return unsignedbv_typet(width);
    } else if(is_signed(b1) && is_signed(b2)) {
      // Again, just need to take the max of the widths.
      unsigned int width = std::max(b1.get_width(), b2.get_width());
      return signedbv_typet(width);
    } else {
      // This is the (slightly) tricky case.  If we have a signed and an
      // unsigned type, we're going to return a signed type.  And to cast
      // an unsigned type to a signed type, we need the signed type to be
      // at least one bit wider than the unsigned type we're casting from.
      unsigned int signed_width = is_signed(t1) ? b1.get_width() :
                                                  b2.get_width();
      unsigned int unsigned_width = is_signed(t1) ? b2.get_width() :
                                                    b1.get_width();
      unsigned_width++;

      unsigned int width = std::max(signed_width, unsigned_width);

      return signedbv_typet(width);
    }
  }

  assert(!"Couldn't join types");
}
