#include <assert.h>
int x;

void g(int i){
  x=i;
}

int main() {
  g(3);
  assert(x==3);
}

