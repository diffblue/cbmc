// A derived class member function must not access a private member of a
// base class ([class.access]/[class.access.base]): in `derived`, the
// base's private `secret` is inaccessible, even when named without an
// explicit object (i.e. implicitly through `this`).  This must be
// rejected, not silently accepted.

struct base
{
private:
  int secret() const
  {
    return 7;
  }
};

struct derived : base
{
  int use()
  {
    return secret();
  }
};

int main()
{
  derived d;
  return d.use();
}
