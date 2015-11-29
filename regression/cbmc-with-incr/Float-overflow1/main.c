int main()
{
  float f=1;

  for(int i=0; i<127; i++)
    f*=2; // should not overflow
}
