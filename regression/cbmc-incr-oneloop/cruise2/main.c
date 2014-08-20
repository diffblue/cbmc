/*******************************************************************************/
/* Cruise controller                                                           */
/* Author: Peter Schrammel                                                     */
/*******************************************************************************/
/* modelled after                                                              */
/*     Robert Bosch GmbH: Bosch Automotive Handbook. Bentley (2007)            */
/* if you reuse this code, please cite also                                    */
/*      Peter Schrammel, Tom Melham, Daniel Kroening. Chaining Test Cases for 
        Reactive System Testing. In Testing Software and Systems
        LNCS Volume 8254, 2013, pp 133-148                                     */
/*******************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

typedef struct state {
  int mode;
  int speed;
  int button;
} t_state;

#define I_BUTTON 1
#define I_ACC 2
#define I_DEC 3
#define I_GAS 4
#define I_BRAKE 5

typedef struct input {
  int signal; 
} t_input;

void init(t_state *s) {
  s->mode = 0;
  s->speed = 0;
  s->button = 0;
}

void compute(t_input* i, t_state *s) {
  if((s->mode==0) && (s->speed==0) && (s->button==0)) {
    if((i->signal==I_ACC)||(i->signal==I_GAS)) s->speed=1;
    else if(i->signal==I_BUTTON) s->button=1;
  }
  else if((s->mode==0) && (s->speed==1) && (s->button==0)) {
    if((i->signal==I_BRAKE)||(i->signal==I_DEC)) s->speed=0;
    else if((i->signal==I_GAS)||(i->signal==I_ACC)) s->speed=2;
    else if(i->signal==I_BUTTON) { s->button=1; s->mode=1; }
  }
  else if((s->mode==0) && (s->speed==0) && (s->button==1)) {
    if((i->signal==I_GAS)||(i->signal==I_ACC)) {s->speed=1; s->mode=1; }
    else if(i->signal==I_BUTTON) s->button=0; 
  }
  else if((s->mode==1) && (s->speed==1) && (s->button==1)) {
    if(i->signal==I_GAS) { s->speed=2; s->mode=2; }
    else if(i->signal==I_BRAKE) { s->speed=0; s->mode=2; }
    else if(i->signal==I_BUTTON) { s->mode=0; s->button=0; }
  }
  else if((s->mode==2) && (s->speed==2) && (s->button==1)) {
    if((i->signal==I_BRAKE)/*||(i->signal==I_DEC)*/) { s->speed=1; s->mode=1; }
    else if(i->signal==I_BUTTON) { s->mode=0; s->button=0; }
  }
  else if((s->mode==2) && (s->speed==0) && (s->button==1)) {
    if((i->signal==I_GAS)||(i->signal==I_ACC)) { s->speed=1; s->mode=1; }
    else if(i->signal==I_BUTTON) { s->mode=0; s->button=0; }
  }
  else if((s->mode==0) && (s->speed==2) && (s->button==0)) {
    if((i->signal==I_BRAKE)||(i->signal==I_DEC)) s->speed=1; 
    else if(i->signal==I_BUTTON) s->button=1; 
  }
  else if((s->mode==0) && (s->speed==2) && (s->button==1)) {
    if((i->signal==I_BRAKE)||(i->signal==I_DEC)) { s->speed=1; s->mode=1; }
    else if(i->signal==I_BUTTON) s->button=0; 
  }
}


extern t_input nondet_input();

void main() {
  t_state s;
  init(&s);
  while(1) {
    t_input i = nondet_input();
    __CPROVER_assume((1<=i.signal) && (i.signal<=5));
    t_state s_old = s;
    compute(&i,&s);
    assert(!(s_old.mode==2 && s_old.speed==2 && i.signal==I_DEC) ||
           s.mode==1);
  }
}
