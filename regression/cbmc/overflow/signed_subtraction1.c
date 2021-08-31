#define INT_MIN (-1 << (sizeof(int) * 8 - 1))

int main()
{
  int a, b, neg;

  // this should not overflow, even not for a=INT_MIN
  b = a - a;

  // this should also not overflow as long as pos<0
  if(neg < 0)
    b = neg - INT_MIN;

  int x, y, z;

  x = INT_MIN + 1;
  y = INT_MIN;
  z = x - y; // neither
}
