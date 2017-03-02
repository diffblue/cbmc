public class covered1
{
  // this is a variable
  int x=1;
  //these are two, one line off the first
  int y=2;
  int z=3;
  //this is part of static init
  static int z0=0;

  //another non-static
  int a;
  int b;
  static boolean odd;

  static
  {
    odd=(z0+1)%2==0;
  }

  covered1(int a, int b)
  {
    this.a=a*b;
    this.b=a+b;
    if(this.a==a)
      z0++;
    else
      odd=!odd;
  }
  // at the back
  int z1=2;
  int z2=3;
  int z3=4;
  //
  static int z4=5;
  int z5=5;
}
