// A new-expression that value-/default-initializes an object selects the
// type's default constructor, which must be accessible at the point of
// the new-expression (N5008 expr.new, class.access).  X's default
// constructor is private, so this must be rejected.

struct X
{
private:
  X()
  {
  }
};

int main()
{
  X *p = new X();
  (void)p;
  return 0;
}
