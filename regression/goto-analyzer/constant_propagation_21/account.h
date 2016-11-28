#ifndef VVLAB_ACCOUNT
#define VVLAB_ACCOUNT

#include <pthread.h>

typedef struct Account {
    char name;
    double amount;
    pthread_mutex_t *lock;
} Account;

Account *newAccount(char nm, double amt);

void deposit(Account *ac, double money);

void withdraw(Account *ac, double money);

void transfer(Account *src, Account *dst, double money);

void lock(pthread_mutex_t *lock);
void unlock(pthread_mutex_t *lock);

#endif
