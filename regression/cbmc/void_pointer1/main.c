char buffer[2];
int length = 2;

void func(void* buf, int len)
{
  while( len-- )
    *(char *)buf++;
}

void main(){
  func(buffer,length);
}
