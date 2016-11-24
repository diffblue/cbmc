extern "C" typedef struct IUnknown IUnknown;

// these are the same
struct IUnknown
{
  int asd;
};

int f(IUnknown *This);

struct AA {
  int i;
};

struct BBB {
  struct asd *p;
} abc;

struct AAA {
  struct asd *q;
} fff;

struct asd
{
  int z;
};

void f()
{
  abc.p=fff.q;
}

int main()
{
  int z;
  
  z=sizeof(struct AA);

}
