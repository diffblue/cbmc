#include <stdio.h>

#define SIZE 10

typedef struct{
    int elemento[SIZE];
    int inicio;
    int fim;
    int quantidade;
} QType;

int inicializa(QType *q) {
	q->inicio=0;
	q->fim=0;
	q->quantidade=0;
}

int empty(QType * q) {
  if (q->inicio == q->fim) { 
	printf("queue is empty\n");
    return -1;
  }
  else return 0;
}

int full(QType * q) {

	if (q->quantidade == SIZE) {  
		printf("queue is full\n");
		return -1;
	} else{
		return 0;
	}
}

int enqueue(QType *q, int x) {
	q->elemento[q->fim] = x;
	q->quantidade++;
	if (q->fim == SIZE) {
		q->fim = 0;
	} else {
		q->fim++;
	}
	return 0;
}

int dequeue(QType *q) {

	int x;

	x = q->elemento[q->inicio];
	q->quantidade--;
	if (q->inicio == SIZE) {
		q->inicio = 0;
	} else { 
		q->inicio++;
	}

	return x;
}


int main(void) {

	QType queue;

	int i,temp;

	inicializa(&queue);

	empty(&queue);

	enqueue(&queue,2);

	empty(&queue);

	enqueue(&queue,4);
	enqueue(&queue,1);
	enqueue(&queue,5);
	enqueue(&queue,3);
	enqueue(&queue,8);
	enqueue(&queue,6);
	enqueue(&queue,7);
	enqueue(&queue,10);
	enqueue(&queue,9);
	
	full(&queue);

	temp = dequeue(&queue);

	printf("temp = %d\n", temp);

	temp = dequeue(&queue);

	printf("temp = %d\n", temp);

	for(i=queue.inicio; i<queue.fim; i++){
		printf("queue[%d] = %d\n", i, queue.elemento[i]);
	}

	return 0;
}
