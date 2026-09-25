int l[10][10];
int g;

int main(void)
{
  if(&l[g + 2][g] == &l[3][3])
    return 1;
  return 0;
}
