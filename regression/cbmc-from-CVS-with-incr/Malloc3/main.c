void *malloc(unsigned size);
void free(void *p);

int main() {
  int *p;
  unsigned int n;

  p=malloc(sizeof(int)*10);

  free(p);
  
  // bad!
  p[1]=1;
}
