// The default constructor selected to default-initialize a non-static
// data member of class type must be accessible in the enclosing
// constructor's context (N5008 class.base.init/12, class.access.base).
// Here member `field` has type `m` whose default constructor is private,
// so `holder`'s constructor cannot default-initialize it: the program is
// ill-formed and must be rejected, not silently accepted.

struct m
{
private:
  m()
  {
  }
};

struct holder
{
  m field;
  holder()
  {
  }
};

int main()
{
  holder h;
  return 0;
}
