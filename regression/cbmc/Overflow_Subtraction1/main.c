#define INT_MIN (-1<<(sizeof(int)*8-1))

int main()
{
  int a, b;
  
  // this should not overflow, even not for a=INT_MIN
  b=a-a;
  
  // this should also not overflow
  b=a-INT_MIN;
}
