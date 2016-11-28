#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <pthread.h>
#include "account.h"

Account *newAccount(char nm, double amt) {
    int err;

    Account *tmp = (Account *) malloc(sizeof(Account));
    tmp->lock = (pthread_mutex_t *) malloc(sizeof(pthread_mutex_t));
    tmp->name = nm;
    tmp->amount = amt;
    if (0 != (err = pthread_mutex_init(tmp->lock, NULL))) {
        fprintf(stderr, "Got error %d from pthread_mutex_init.\n", err);
        exit(-1);
    }
    return tmp;
}

void deposit(Account *ac, double money) {
    pthread_mutex_lock(ac->lock);

    ac->amount += money;
    //printf("Deposited $%0.2f in %c.\n", money, ac->name);

    pthread_mutex_unlock(ac->lock);
}

void withdraw(Account *ac, double money) {
    pthread_mutex_lock(ac->lock);

    ac->amount -= money;
    //printf("Withdrew $%0.2f from %c.\n", money, ac->name);

    pthread_mutex_unlock(ac->lock);
}

void transfer(Account *src, Account *dst, double money) {
    pthread_mutex_lock(src->lock);

    src->amount -= money;

    if (src->name == 'D') {
        dst->amount += money;
    } else {
        pthread_mutex_lock(dst->lock);
        dst->amount +=money;
        pthread_mutex_unlock(dst->lock);
    }
    //printf("Transfered $%0.2f from %c to %c\n", money, src->name, dst->name);

    pthread_mutex_unlock(src->lock);
}

void lock(pthread_mutex_t *lock) {
#if 0
    int err;
    if (0 != (err = pthread_mutex_lock(lock))) {
        fprintf(stderr, "Got error %d from pthread_mutex_lock.\n", err);
        exit(-1);
    }
#endif
}

void unlock(pthread_mutex_t *lock) {
#if 0
    int err;
    if (0 != (err = pthread_mutex_unlock(lock))) {
        fprintf(stderr, "Got error %d from pthread_mutex_unlock.\n", err);
        exit(-1);
    }
#endif
}
        
