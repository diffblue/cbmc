
typedef struct tag_struct_name
{
  int x;
  float y;
} MYSTRUCT;

struct tag_struct_name fun()
{
  struct tag_struct_name return_variable = { .x = 1, .y = 3.14f};
  return return_variable;
}

MYSTRUCT fun2()
{
  MYSTRUCT return_variable = { .x = 1, .y = 3.14f};
  return return_variable;
}


