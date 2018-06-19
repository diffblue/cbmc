// This is a benchmark for the full-slicer
// It is a simplified version of end-to-end regression test
// 'taint_crossing_substr_and_concatenation' of the security-scanner.

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

extern int CProver_nondetInt();

struct object
{
  bool X;
  bool SBX;
};

struct String
{
  struct object super;
};

struct StringBuilder
{
  struct object super;
};

struct String *source()
{
  return (struct String *)malloc(sizeof(struct String));
}

struct StringBuilder *append(struct StringBuilder *sb, struct String *s)
{
  return sb;
}

struct String *toString(struct StringBuilder *sb)
{
  return (struct String *)malloc(sizeof(struct String));
}

int main()
{
  struct StringBuilder *tmp1, *sb;
  struct String *tmp2, *tainted;

  sb = (struct StringBuilder *)malloc(sizeof(struct StringBuilder));
  tainted = source();
  tainted->super.X = true;
  tmp1 = append(sb, tainted);

  // Next 2 lines are wrongly sliced away!
  if(tainted->super.X)
    sb->super.SBX = true;

  tmp2 = toString(tmp1);
  if(tmp1->super.SBX)
    tmp2->super.X = true;
  if(tmp2->super.X)
    assert(false);
  return 0;
}
