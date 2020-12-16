struct
{
  int x : 2;
} a;
unsigned b;
_Bool c;
int main()
{
  c |= a.x;
  b |= a;
}
