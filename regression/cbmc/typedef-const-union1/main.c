
typedef union tag_union_name
{
  int x;
  float y;
} MYUNION;

void fun()
{
  const union tag_union_name tag_union_var = {1};
  const MYUNION myunion_var = {.y = 2.1f};
}
