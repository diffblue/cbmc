
typedef union tag_union_name
{
  int x;
  float y;
} MYUNION;

union tag_union_name fun()
{
  union tag_union_name return_variable = {1};
  return return_variable;
}

MYUNION fun2()
{
  MYUNION return_variable = {1};
  return return_variable;
}


