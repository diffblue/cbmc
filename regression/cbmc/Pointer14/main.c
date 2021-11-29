void *malloc(__CPROVER_size_t);

enum blockstate
{
  S1,
  S2
};

typedef struct
{
  enum blockstate bs;
  int id;
  int version;
} block;

typedef struct blocknode
{
  block *b;
  struct blocknode *next;
} blocknode;

typedef blocknode *bl;

int main()
{
  block *bp = (block *)(malloc(sizeof(block)));
  bl l = (bl)(malloc(sizeof(blocknode)));
  bp->version = 1;
  l->b = bp;
  l->b->version = l->b->version + 1;
  // this should fail
  assert((l->b->version) == 1);
}
