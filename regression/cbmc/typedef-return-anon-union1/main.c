
typedef union
{
  int x;
  float y;
} MYUNION;


MYUNION fun()
{
  MYUNION return_variable = {1};
  return return_variable;
}


