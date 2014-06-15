typedef unsigned char BOOLEAN;

typedef unsigned char INT8U;

typedef signed char INT8S;

typedef unsigned int INT16U;

typedef unsigned long INT32U;

typedef unsigned int OS_STK;

typedef INT16U OS_FLAGS;

struct os_event {
   INT8U OSEventType ;
   INT8U OSEventGrp ;
   INT16U OSEventCnt ;
   void *OSEventPtr ;
   INT8U OSEventTbl[8] ;
   char OSEventName[32] ;
};

typedef struct os_event OS_EVENT;

OS_EVENT OSEventTbl[10] ;

int main(void)
{
  int x;
  
  x=sizeof(OSEventTbl);
}
