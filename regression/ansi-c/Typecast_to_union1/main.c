// typecast to union is GCC only
#ifdef __GNUC__

union U
{
  int i;
  double d;
};

int main()
{
  union U u;
  
  u=(union U)(1>2); // the relational operators return "int"
  u=(union U)(1 && 1);
  u=(union U)1.0; // the literal is double, not float
}

#else

int main()
{
}

#endif
