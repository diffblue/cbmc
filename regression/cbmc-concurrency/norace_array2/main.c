#include <assert.h>
#include <pthread.h>
#include <stdlib.h>

unsigned long data[2];

void *thread0(void *arg)
{
    data[0] = 1;
    return NULL;
}

void *thread1(void *arg)
{
    data[1] = 1;
    return NULL;
}

int main(int argc, char *argv[])
{
    pthread_t t0;
    pthread_t t1;

    pthread_create(&t0, NULL, thread0, NULL);
    pthread_create(&t1, NULL, thread1, NULL);
    pthread_join(t0, NULL);
    pthread_join(t1, NULL);

    assert(data[0] == 1);
    assert(data[1] == 1);

    return 0;
}
