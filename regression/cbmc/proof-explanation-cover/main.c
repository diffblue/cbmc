typedef struct
{
  int balance;
  int is_locked;
} account_t;

int withdraw(account_t *acc, int amount)
{
  if(acc->is_locked)
    return -1;

  if(amount <= 0)
    return -2;

  if(amount > acc->balance)
    return -3;

  acc->balance -= amount;
  return 0;
}

int main()
{
  account_t acc;
  acc.balance = 100;
  acc.is_locked = 0;

  int result = withdraw(&acc, 50);
}
