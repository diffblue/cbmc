extern void this_is_ok;

struct a
{
#ifdef void_member
  void b;
#else
  int b;
#endif
};
struct a *ae;
void d()
{
  ae->b;
}
#ifdef void_global
void x;
#endif
int main()
{
  void v;
  d();
}
