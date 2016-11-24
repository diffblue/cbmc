struct listt
{
  int content;
  struct listt *next;
};

typedef struct listt listt;
 
int main ()
{
  listt el0, el1, *ppp1, *ppp2;
  el0.next = 0;
  listt *head = &el1;
  head->next = &el0;
  ppp1=head->next;
  ppp2=ppp1->next;
  assert(ppp2==0);
}
