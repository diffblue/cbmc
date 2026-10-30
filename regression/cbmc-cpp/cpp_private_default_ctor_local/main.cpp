// The default constructor selected to default-initialize an object must
// be accessible at the point of declaration (N5008 dcl.init,
// class.access).  Here X's default constructor is private, so declaring
// a local X is ill-formed and must be rejected, not silently accepted.

struct X
{
private:
  X()
  {
  }
};

int main()
{
  X x;
  (void)&x;
  return 0;
}
