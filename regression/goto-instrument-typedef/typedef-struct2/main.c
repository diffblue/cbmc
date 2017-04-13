
typedef struct tag_struct_name
{
  int x;
  float y;
} MYSTRUCT;

void fun()
{
  struct tag_struct_name tag_struct_var = {.x = 1, .y = 3.14f};
  MYSTRUCT mystruct_var = {.x = 3, .y = 2.1f};
}
