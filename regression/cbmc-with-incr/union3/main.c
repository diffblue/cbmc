int my_func(int stat_loc)
{
  // this is a 'temporary union', yet another gcc extension
  return ((union { __typeof__(stat_loc) __in; int __i; })
    { .__in =(stat_loc) }).__i;
}

int main(void)
{
  int x;
  assert(my_func(x)==x);
  
  // this is yet another gcc extension
  union my_U
  {
    int z;
    char ch;
    float f;
  } union_object;
  
  float some_float=1.5;
  
  union_object=(union my_U)some_float;
  
  assert(union_object.f==1.5);
} 
