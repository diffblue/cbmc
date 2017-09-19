
extern int getone();

#include <assert.h>

int main(int argc, char** argv) {
  assert(getone()==1);
}

int altmain() {
  assert(getone()==0);
}
