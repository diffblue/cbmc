#include <assert.h>

// do both orderings

extern const char *abc1[];
const char *abc1[] = {"Hallo", "Welt"};

const char *abc2[] = {"Hallo", "Welt"};
extern const char *abc2[];

// modifiers

static const char * const a1[] = { "abc" };
static const char * const a2[] = { "abc", "" };

char string_array[1][1][5] = {"1234"};

int main()
{
  // both must be complete
  sizeof(abc1);
  sizeof(abc2);
  
  assert(string_array[0][0][0]=='1');
  assert(string_array[0][0][1]=='2');
  assert(string_array[0][0][2]=='3');
  assert(string_array[0][0][3]=='4');
  assert(string_array[0][0][4]==0);
}

