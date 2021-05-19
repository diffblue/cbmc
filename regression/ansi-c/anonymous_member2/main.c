#define static_assert(x) struct {char some[(x) ? 1 : -1]; }

struct a
{
};
struct c
{
  struct a;
  void *d;
} e =
  {
#ifdef not_permitted
    {},
#endif
    0},
  e2;
struct
{
  struct c f;
} * g;
int main()
{
  g->f;
  static_assert(sizeof(e) == sizeof(void *));
}
