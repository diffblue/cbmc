void *stat()
{
}

void *lstat()
{
}

int main()
{
 int link_p;
 (void*(*)(const char*,void*))&(*(link_p ? &stat : &lstat));
  &(*(&lstat));
  const char *f=&(__FUNCTION__[2]);
  char *p=&(char){':'};
}

