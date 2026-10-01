void cb(int)
{
}
int main()
{
  // [dcl.init.ref]/5: `&cb' is a prvalue of type void (*)(int); an lvalue
  // reference to function cannot bind to it
  void (&r)(int) = &cb;
  r(1);
}
