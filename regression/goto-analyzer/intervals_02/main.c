
int main(){
  int x;
  if (x > 0 && x < 20) {
    __CPROVER_assert(x > -10 && x < 100, "x > -10 && x < 100");
  }
  return 0;
}
