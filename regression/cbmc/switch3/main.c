char nondet_char();

int main()
{
  char ch=nondet_char();
  
  switch(ch)
  {
  case 'P':
  case 'p':
    assert(ch==80 || ch==112);
    break;
  
  default:
    assert(ch!=80 && ch!=112);  
  }
}
