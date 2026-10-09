struct Node
{
  Node *next;
  int val;
};

int sum(Node *head)
{
  int s = 0;
  while(Node *p = head)
  {
    s += p->val;
    head = p->next;
  }
  return s;
}

int main()
{
  return 0;
}
