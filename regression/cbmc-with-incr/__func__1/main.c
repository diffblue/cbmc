int main()
{
  char ch0, ch1, ch2, ch3, ch4;
  
  ch0=__func__[0];
  ch1=__func__[1];
  ch2=__func__[2];
  ch3=__func__[3];
  ch4=__func__[4];
  
  assert(ch0=='m');
  assert(ch1=='a');
  assert(ch2=='i');
  assert(ch3=='n');
  assert(ch4==0);

  return 0;
}
