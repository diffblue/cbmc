
typedef struct
{
  int x;
  float y;
} MYSTRUCT;

void fun()
{
  MYSTRUCT mystruct_var  = {.x = 10, .y = 3.1f}, another_mystruct_var = {.x = 3, .y = 2.1f};
}
