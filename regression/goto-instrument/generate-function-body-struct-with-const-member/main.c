#include <assert.h>

struct WithConstMember
{
  int non_const;
  const int is_const;
};

struct WithConstMember globalStruct = {10, 20};
void havoc_struct(struct WithConstMember *s);

int main(void)
{
  struct WithConstMember paramStruct = {11, 21};
  havoc_struct(&paramStruct);
  assert(globalStruct.non_const == 10);
  assert(globalStruct.is_const == 20);
  assert(paramStruct.non_const == 11);
  assert(paramStruct.is_const == 21);
  return 0;
}
