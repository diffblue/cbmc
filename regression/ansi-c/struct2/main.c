#define QSIZE	10

typedef struct queue {
	int length;
	int size;
	int data[QSIZE];
} QUEUE;

QUEUE *queue_create()
{
	QUEUE q;

	q.length = 0;

	return &q;
}

int main() {
	QUEUE *ptr = queue_create();
}
