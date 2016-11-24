typedef unsigned char BOOLEAN;
typedef unsigned int INT16U;

typedef struct {
	int x;
} OS_EVENT;

OS_EVENT *OSEventFreeList;

OS_EVENT *OSQCreate(void **start, INT16U size);

typedef struct os_q {
    void **OSQStart;
} OS_Q;

static OS_Q *OSQFreeList;

OS_EVENT *OSQCreate (void **start, INT16U size)
{
    OS_EVENT *pevent;
    OS_Q *pq;

    pevent = OSEventFreeList;
    if (pevent != (OS_EVENT *)0) {
        pq = OSQFreeList;
        if (pq != (OS_Q *)0) {
            pq->OSQStart = start;
        }
    }
    return (pevent);
}

OS_EVENT *QSem;
void *QMsgTbl[2];

int main() {
        QSem = OSQCreate(&QMsgTbl[0], 2);
}
