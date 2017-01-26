// Needs context sensitivity

void memcpy(void* t_tgt, const void* t_src, int t_sz) {

  int i;

  for (i=0; i < t_sz; i+=sizeof(int))
    *((int*)t_tgt) = *(int*)t_src;

  i -= sizeof(int);

  for (;i < t_sz; i++)
    *((char*)t_tgt) = *((char*)t_src);
}

int main()
{
  memcpy(0, 0, 0);
  return 0;
}

