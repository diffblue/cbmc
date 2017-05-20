
typedef struct
{
  int x;
  float y;
} MYSTRUCT;

MYSTRUCT fun()
{
  MYSTRUCT return_variable = {.x = 1, .y = 3.14f};
  return return_variable;
}
