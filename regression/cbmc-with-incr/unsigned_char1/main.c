char x;
signed char sx;

int main ()
{
  x=-1;
  // this will only work if 'char' is unsigned
  assert(x==255);

  // a regular one
  sx=-1;
  assert(sx==-1);
}
