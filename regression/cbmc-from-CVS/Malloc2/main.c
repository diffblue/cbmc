typedef unsigned int    size_t;
typedef int             ssize_t;
typedef int             atomic_t;
typedef unsigned        gfp_t;

struct pp_struct {
  atomic_t irqc;
};

void *malloc(size_t size);

void * kmalloc(size_t size, gfp_t flags)
{
  return malloc(size);
}

int main(void)
{
  struct pp_struct *pp;
  atomic_t *pp2;

  pp = kmalloc (sizeof (struct pp_struct), 10);

  // This works:
  // pp = malloc (sizeof (struct pp_struct));

  if (!pp)
    return -10;
    
  pp2=&(pp->irqc);
  
  //*(&(pp->irqc))=0;
  
  return 0;
}
