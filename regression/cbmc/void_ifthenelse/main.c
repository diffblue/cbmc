int g;

void f()
{
  g=1;
}

int main() {
  assert(g==0);
  
  g==0?f():g;

  assert(g==1);
}
