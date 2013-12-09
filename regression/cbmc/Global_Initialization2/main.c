#include <assert.h>

int A1[];

// tentative definition
int A2[2];
int A2[] = { 1 };

// another valid tenatitive definition
static int A3[3];
static int A3[] = { 1, 2 };

int main()
{
  // C standard 6.9.2, paragraphs 2 and 5
  assert(A1[0]==0);

  // C standard 6.7.9, paragraph 21
  assert(A2[1]==0);

  assert(sizeof(A3)==3*sizeof(int));

  return 0;
}

