// struct Inner is incomplete in this translation unit.

struct Inner;

struct S
{
  union
  {
    struct Inner *via_struct;
    int *via_int;
  } u;
  int sentinel;
};

int points_to(struct S *p, struct Inner *inner)
{
  return p->u.via_struct == inner && p->sentinel == 42;
}
