int g;
int **p;

struct
{
  int m;
} s;

struct B {
	static int x;
};

int B::x;

char a[10];

int main()
{
  assert(g==0);
  assert(p==0);
  assert(s.m==0);
  assert(a[3]==0);
  assert(B::x==0);
}
