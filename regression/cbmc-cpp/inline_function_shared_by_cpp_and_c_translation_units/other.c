#include "shared.h"
int c_side(struct stream *s)
{
  return stream_position(s) + 1;
}
