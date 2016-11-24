#include <assert.h>

int main()
{
  int signed_int=1;
  float a_float=1;
  double a_double=1;
  long long long_long_int=1;

  struct some
  {
    int f;
  };
  
  assert(*(unsigned long long int *)&long_long_int==1);
  assert(*(unsigned int *)&signed_int==1);
  assert(((struct some *)&signed_int)->f==1);
  assert(*(int *)&a_float==1065353216);
  assert(*(long long int *)&a_double==4607182418800017408l);
  
  // other direction
  signed_int=1065353216;
  assert(*(float *)&signed_int==1.0f);
}
