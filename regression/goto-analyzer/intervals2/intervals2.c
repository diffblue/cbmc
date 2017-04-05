#include <assert.h>

int main(){
  int x;
  if (x > 0 && x < 20) {
    //if (x < 20) {
      assert(x > -10 && x < 100);
    //}
  }
  return 0;
}
