typedef int X;
int Y;

int main()
{
  int z;
  int *p;

  (X) + z; // this is a typecast
  (Y) + z; // this is an addition
  
  (X) - z; // this is a typecast
  (Y) - z; // this is a subtraction
  
  (X) & z; // this is a typecast
  (Y) & z; // this is a bitwise and
  
  (X) * p; // this is a typecast
}
