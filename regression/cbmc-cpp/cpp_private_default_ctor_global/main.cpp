// The default constructor selected to default-initialize a namespace-
// scope (static-storage) object must be accessible at the point of
// declaration (N5008 dcl.init, class.access).  X's default constructor
// is private, so this global definition is ill-formed and must be
// rejected, not silently accepted (its construction is otherwise emitted
// during static initialization, where access control is disabled).

struct X
{
private:
  X()
  {
  }
};

X g;

int main()
{
  (void)&g;
  return 0;
}
