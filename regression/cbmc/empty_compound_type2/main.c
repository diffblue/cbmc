struct B
{
} b[1];
struct c
{
  void *d;
} e = {b};
struct
{
  struct c f;
} * g;
int main()
{
  g->f;
}
