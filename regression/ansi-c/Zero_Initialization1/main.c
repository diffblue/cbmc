// will remain incomplete
extern struct foo x;

// never gets a body
extern void foo(struct foo *arg);

// but called anyway
extern inline void bar()
{
  foo(&x);
}

// similar with an incomplete array
extern char some_array[];
 
// similar with a union
extern union moo y;

int main()
{
}
