typedef struct _this {
  int ndim;
  void *voidregion;
} This;

#define NDIM t->ndim

void Split(This *t)
{
typedef struct region {
  int bounds[NDIM];
} Region;

  // The following has to be equivalent to
  // Region *region;
  // region = (Region*)t->voidregion;
  Region *region = (Region*)t->voidregion;
  unsigned size=sizeof(region->bounds);
  assert(size==NDIM*sizeof(int));
}

int main()
{
  struct {
    int bounds[42];
  } s;
  This t={ .ndim=42, .voidregion=&s };
  Split(&t);
  return 0;
}

