namespace some_namespace
{
  class X;
};

// This is allowed, as the class tag is already there.
class some_namespace::X
{
};

// Perhaps surprisingly, the same does not seem to be true for enum tags on g++,
// but Visual studio is happy to do this.

int main()
{
}
