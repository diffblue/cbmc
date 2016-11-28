#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include "account.h"


#define ACCTS 5

static Account *accounts[ACCTS];

void *threadWork(void *param) {
//    int tid = *((int *)param);
	int tid, *tidptr;  
	tidptr=(int *)param;
  	tid=*tidptr;

    deposit(accounts[tid], 300);
    transfer(accounts[tid], accounts[(tid+1)%ACCTS], 10);  
    deposit(accounts[tid], 10);
    transfer(accounts[tid], accounts[(tid+2)%ACCTS], 10);  
    withdraw(accounts[tid], 20);    
    deposit(accounts[tid], 10);    
    transfer(accounts[tid], accounts[(tid+1)%ACCTS], 10);  
    withdraw(accounts[tid], 100);

    //printf("Thread %d is done.\n", tid);

    return NULL;
}


int main(int argc, char *argv[]) {
    int i, err, tmp;
    char names[ACCTS] = {'A','B','C','D','E'};

    pthread_t pool[ACCTS];
    for (i = 0; i < ACCTS; i++) {
        accounts[i] = (Account *) malloc(sizeof(Account));
        accounts[i] = newAccount(names[i], 100);
    }

    for (i = 0; i < ACCTS; i++) {
        if ((err = pthread_create(&pool[i], NULL, &threadWork, /*(void *)i*/&i)))
        {
            fprintf(stderr, "Problem creating thread pool.\n");
            fprintf(stderr, "pthread error: %d\n", err);
            exit(-1);
        }
    }

    for (i = 0; i < ACCTS; i++) {
        if (0 != (err = pthread_join(pool[i], NULL)))
        {
            fprintf(stderr, "pthread join error: %d\n", err);
            exit(-1);
        }
    }


    for (i = 0; i < ACCTS; i++) {
        if (accounts[i]->amount != 300) {
            printf("Bug found!\n");
			assert(0);
        }
    }

    return 0;
}

