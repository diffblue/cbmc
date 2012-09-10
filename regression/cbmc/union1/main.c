union u_type
{
  int i;
  char ch;
};

int main() {
  union u_type u;
  
  u.i=1;
  assert(u.i==1);
  
  u.ch=2;
  assert(u.ch==2);
}
