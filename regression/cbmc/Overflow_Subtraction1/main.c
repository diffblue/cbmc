int main()
{
  int a, b;
  
  // this should not overflow, even not for a=INT_MIN
  b=a-a;
}
