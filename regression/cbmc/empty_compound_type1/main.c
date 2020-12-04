union a {
};
struct
{
  union a;
} b;
struct c
{
  int cli;
};
void e(struct c *f)
{
  int a = f->cli;
}
main()
{
  // pass a pointer to an incompatible type
  e(&b);
}
