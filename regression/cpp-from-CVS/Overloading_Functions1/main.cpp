// get closest match

struct T
{
public:
  T():x(0) { }

  int x;
};

int f(int i) { return 1; }
int f(const int *p) { return 2; }
int f(char i) { return 3; }
int f(struct T &t) { return 4; }
int f(const struct T &t) { return 5; }

int main()
{
  int i;
  char ch;
  T t;
  const T const_t;

  assert(f(i)==1);
  assert(f(&i)==2);
  assert(f(ch)==3);
  assert(f(t)==4);
  assert(f(const_t)==5);
}
