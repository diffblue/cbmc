#include <assert.h>
#include <stdio.h>

typedef int T[];

struct f
{
  int w;
  T x;
};

static struct f before = {0xdeadbeef};
static struct f f = {4, {0, 1, 2, 3, 4}};
static struct f after = {0xcafecafe};

struct St
{
  char c;
  int d[];
};
struct St s = {'a', {11, 5}};

int main()
{
  int i;
  for(i = 0; i < f.w; ++i)
  {
    if(f.x[i] != i)
    {
      assert(0);
    }
  }
  assert(sizeof(f) == sizeof(struct f));
  assert(before.w == 0xdeadbeef);
  assert(after.w == 0xcafecafe);
  printf("%llx\n", &before);
  printf("%llx\n", &f);
  printf("%llx\n", &after);

  unsigned char c;
  c = c && 1;
  assert(c == 0 || c == 1);
  assert(s.d[1] == 5);
  s.d[1] += c;
  assert(s.d[1] < 8);
  assert(s.d[0] == 11);

  return 0;
}
