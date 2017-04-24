#define FAIL

#include <assert.h>


int BLOCK1 = 0;
int BLOCK2 = 0;
int BLOCK3 = 0;
int BLOCK4 = 0;
int BLOCK5 = 0;
int BLOCK6 = 0;
int BLOCK7 = 0;
int BLOCK8 = 0;
int BLOCK9 = 0;
int BLOCK10 = 0;
int BLOCK11 = 0;
int BLOCK12 = 0;
int BLOCK13 = 0;
int BLOCK14 = 0;
int BLOCK15 = 0;
int BLOCK16 = 0;
int BLOCK17 = 0;
int BLOCK18 = 0;
int BLOCK19 = 0;
int BLOCK20 = 0;
int BLOCK21 = 0;
int BLOCK22 = 0;
int BLOCK23 = 0;
int BLOCK24 = 0;
int BLOCK25 = 0;
int BLOCK26 = 0;
int BLOCK27 = 0;
int BLOCK28 = 0;
int BLOCK29 = 0;
int BLOCK30 = 0;
int BLOCK31 = 0;
int BLOCK32 = 0;
int BLOCK33 = 0;
int BLOCK34 = 0;
int BLOCK35 = 0;
int BLOCK36 = 0;
int BLOCK37 = 0;
int BLOCK38 = 0;
int BLOCK39 = 0;
int BLOCK40 = 0;
int BLOCK41 = 0;
int BLOCK42 = 0;
int BLOCK43 = 0;
int BLOCK44 = 0;
int BLOCK45 = 0;
int BLOCK46 = 0;
int BLOCK47 = 0;
int BLOCK48 = 0;
int BLOCK49 = 0;
int BLOCK50 = 0;
int BLOCK51 = 0;
int BLOCK52 = 0;
int BLOCK53 = 0;
int BLOCK54 = 0;
int BLOCK55 = 0;
int BLOCK56 = 0;
int BLOCK57 = 0;
int BLOCK58 = 0;
int BLOCK59 = 0;
int BLOCK60 = 0;
int BLOCK61 = 0;
int BLOCK62 = 0;
int BLOCK63 = 0;
int BLOCK64 = 0;
int BLOCK65 = 0;
int BLOCK66 = 0;
int BLOCK67 = 0;
int BLOCK68 = 0;
int BLOCK69 = 0;
int BLOCK70 = 0;
int BLOCK71 = 0;
int BLOCK72 = 0;
int BLOCK73 = 0;
int BLOCK74 = 0;
int BLOCK75 = 0;
int BLOCK76 = 0;
int BLOCK77 = 0;
int BLOCK78 = 0;
int BLOCK79 = 0;
int BLOCK80 = 0;
int BLOCK81 = 0;
int BLOCK82 = 0;
int BLOCK83 = 0;
int BLOCK84 = 0;
int BLOCK85 = 0;
int BLOCK86 = 0;
int BLOCK87 = 0;
int BLOCK88 = 0;
int BLOCK89 = 0;
int BLOCK90 = 0;
int BLOCK91 = 0;
int BLOCK92 = 0;
int BLOCK93 = 0;
int BLOCK94 = 0;
int BLOCK95 = 0;
int BLOCK96 = 0;
int BLOCK97 = 0;
int BLOCK98 = 0;
int BLOCK99 = 0;
int BLOCK100 = 0;
int BLOCK101 = 0;
int BLOCK102 = 0;
int BLOCK103 = 0;
int BLOCK104 = 0;
int BLOCK105 = 0;
int BLOCK106 = 0;
int BLOCK107 = 0;
int BLOCK108 = 0;
int BLOCK109 = 0;
int BLOCK110 = 0;
int BLOCK111 = 0;
int BLOCK112 = 0;
int BLOCK113 = 0;
int BLOCK114 = 0;
int BLOCK115 = 0;
int BLOCK116 = 0;
int BLOCK117 = 0;

// NB there are three calls to error in the program. 91 is the bug . 5 10 48 are the error statments. 
// paths always go through 5|10|48, but not always thru 5, and not always through 48, but always through 7
// NB PASSING TRACES are anything that doesnt violate at least one spec. nb "degrees" of passing and failing? 
// BLOCK5==1 && BLOCK7==1 && BLOCK48==1
void error(void) 
{ 
 #ifdef FAIL
   assert(0);//SUT
 #endif
}


void immediate_notify(void) ;
int max_loop ;
int num ;
int i  ;
int e  ;
int timer ;
char data_0  ;
char data_1  ;
char read_data(int i___0 ) 
{ BLOCK1 = 1;

  char c ;
  char __retres3 ;

  {
  if (i___0 == 0) {  BLOCK2 = 1;
    __retres3 = data_0;
    goto return_label;
  } else { BLOCK3 = 1;
    //__CPROVER_assert(i___0==1, "i___0==1 A");
    if (i___0 == 1) { BLOCK4 = 1;
      __retres3 = data_1;
      goto return_label;
    } else { BLOCK5 = 1;
      {
      //  error();
      }
    }
  }
  __retres3 = c;
  return_label: /* CIL Label */ 
  
  // PASS ASSERTION1
  #ifdef PASS1
  assert(BLOCK5!=0);
  //if (BLOCK5==0)
  //{
  //  assert(0);//SUT
  //}
  #endif
  
  return (__retres3);
}
}
void write_data(int i___0 , char c ) 
{  BLOCK6 = 1;

  {
  if (i___0 == 0) { BLOCK7 = 1;
    data_0 = c;
  } else { BLOCK8 = 1;
    _Bool flag;
    //if(flag)
    __CPROVER_assert(i___0==1, "i___0==1 B");
    //else
    //__CPROVER_assert(!(i___0==1), "i___0==1 B");
    if (i___0 == 1) { BLOCK9 = 1;
      data_1 = c;
    } else { BLOCK10 = 1;
      {
	//error();
      }
    }
  }

    // PASS ASSERTION2
   #ifdef PASS2
  if (BLOCK10==0)
  {
    assert(0);//SUT
  }
  #endif
  
  return;
}
}
int P_1_pc;
int P_1_st  ;
int P_1_i  ;
int P_1_ev  ;
void P_1(void) 
{ BLOCK11 = 1;

  {
  if ((int )P_1_pc == 0) { BLOCK12 = 1;
    goto P_1_ENTRY_LOC;
  } else { BLOCK13 = 1;
    if ((int )P_1_pc == 1) { BLOCK14 = 1;
      goto P_1_WAIT_LOC;
    } else { BLOCK15 = 1;

    }
  }
  P_1_ENTRY_LOC: 
  {
  while (i < max_loop) { BLOCK16 = 1;
    while_0_continue: /* CIL Label */ ;
    { BLOCK17 = 1;
    write_data(num, 'A');
    num += 1;
    P_1_pc = 1;
    P_1_st = 2;
    }

    goto return_label;
    P_1_WAIT_LOC: ;
  }
  while_0_break:  BLOCK18 = 1; /* CIL Label */ ;
  }
  P_1_st = 2;

  return_label: BLOCK19 = 1;  /* CIL Label */ 
  return;
} 
}
int is_P_1_triggered(void) 
{ int __retres1 ;
 BLOCK20 = 1; 
  {
  if ((int )P_1_pc == 1) {  BLOCK21 = 1; 
    if ((int )P_1_ev == 1) { BLOCK22 = 1; 
      __retres1 = 1;
      goto return_label;
    } else { BLOCK23 = 1; 

    }
  } else { BLOCK23 = 1; 

  }
  __retres1 = 0;
  return_label: /* CIL Label */ 
  return (__retres1);
}
}
int P_2_pc  ;
int P_2_st  ;
int P_2_i  ;
int P_2_ev  ;
void P_2(void) 
{ BLOCK24 = 1; 

  {
  if ((int )P_2_pc == 0) { BLOCK25 = 1; 
    goto P_2_ENTRY_LOC;
  } else { BLOCK26 = 1; 
    if ((int )P_2_pc == 1) { BLOCK27 = 1; 
      goto P_2_WAIT_LOC;
    } else { BLOCK28 = 1; 

    }
  }
  P_2_ENTRY_LOC: 
  {  BLOCK29 = 1;
  while (i < max_loop) { 
    while_1_continue: /* CIL Label */ ;
    {BLOCK30 = 1;
    write_data(num, 'B');
    num += 1;
    }
    if (timer) { BLOCK31 = 1; 
      {
      timer = 0;
      e = 1;
      immediate_notify();
      e = 2;
      }
    } else { BLOCK32 = 1;

    }
    P_2_pc = 1;
    P_2_st = 2;

    goto return_label;
    P_2_WAIT_LOC: ;
  }
  while_1_break: /* CIL Label */ ;
  }
  P_2_st = 2;

  return_label: /* CIL Label */ 
  return;
}
}
int is_P_2_triggered(void) 
{ int __retres1 ;
  BLOCK33 = 1;
  
  {
  if ((int )P_2_pc == 1) {   BLOCK34 = 1;
    if ((int )P_2_ev == 1) {   BLOCK35 = 1;
      __retres1 = 1;
      goto return_label;
    } else { BLOCK36 = 1;

    }
  } else { BLOCK37 = 1;

  }
  __retres1 = 0;
  return_label: /* CIL Label */ 
  return (__retres1);
}
}
int C_1_pc  ;
int C_1_st  ;
int C_1_i  ;
int C_1_ev  ;
int C_1_pr  ;
void C_1(void) 
{ char c ;
BLOCK38 = 1;
  {
  if ((int )C_1_pc == 0) {BLOCK39 = 1;
    goto C_1_ENTRY_LOC;
  } else { BLOCK40 = 1;
    if ((int )C_1_pc == 1) {BLOCK41 = 1;
      goto C_1_WAIT_1_LOC;
    } else { BLOCK42 = 1;
      if ((int )C_1_pc == 2) { BLOCK43 = 1;
        goto C_1_WAIT_2_LOC;
      } else { BLOCK44 = 1;

      }
    }
  }
  C_1_ENTRY_LOC: 
  {
  while (i < max_loop) {BLOCK45 = 1;
    while_2_continue: /* CIL Label */ ;
    if (num == 0) {BLOCK46 = 1;
      timer = 1;
      i += 1;
      C_1_pc = 1;
      C_1_st = 2;

      goto return_label;
      C_1_WAIT_1_LOC: ;
    } else {BLOCK47 = 1;

    }
    num -= 1;
    //__CPROVER_assert(num>=0, "num>=0 A");
    if (! (num >= 0)) {
      {BLOCK48 = 1;
	//error();
      }
    } else {BLOCK49 = 1;

    }
    {BLOCK50 = 1;
    c = read_data(num);
    i += 1;
    C_1_pc = 2;
    C_1_st = 2;
    }

      // PASS ASSERTION3
   #ifdef PASS3
  if (BLOCK48==0)
  {
    assert(0);//SUT
  }
  #endif
  
    goto return_label;
    C_1_WAIT_2_LOC: ;
  }
  
  while_2_break: /* CIL Label */ ;
  }
  C_1_st = 2;

  return_label: /* CIL Label */ 
 
  return;
}
}
int is_C_1_triggered(void) 
{ int __retres1 ; BLOCK51 = 1;

  {
  if ((int )C_1_pc == 1) { BLOCK52 = 1;
    if ((int )e == 1) { BLOCK53 = 1;
      __retres1 = 1;
      goto return_label;
    } else { BLOCK54 = 1;

    }
  } else {

  }
  if ((int )C_1_pc == 2) { BLOCK55 = 1;
    if ((int )C_1_ev == 1) { BLOCK56 = 1;
      __retres1 = 1;
      goto return_label; 
    } else { BLOCK57 = 1;

    }
  } else { BLOCK58 = 1;

  }
  __retres1 = 0;
  return_label: /* CIL Label */ 
  return (__retres1);
}
}
void update_channels(void) 
{ 
  BLOCK59 = 1;


  return;

}
void init_threads(void) 
{ BLOCK60 = 1;

  {
  if ((int )P_1_i == 1) { BLOCK61 = 1;
    P_1_st = 0;
  } else { BLOCK62 = 1;
    P_1_st = 2;
  }
  if ((int )P_2_i == 1) { BLOCK63 = 1;
    P_2_st = 0;
  } else {  BLOCK64 = 1;
    P_2_st = 2;
  }
  if ((int )C_1_i == 1) { BLOCK65 = 1;
    C_1_st = 0;
  } else { BLOCK66 = 1;
    C_1_st = 2;
  }

  return;
}
}
int exists_runnable_thread(void) 
{ int __retres1 ;

  {
  if ((int )P_1_st == 0) { BLOCK67 = 1;
    __retres1 = 1;
    goto return_label;
  } else { BLOCK68 = 1;
    if ((int )P_2_st == 0) { BLOCK69 = 1;
      __retres1 = 1;
      goto return_label;
    } else { BLOCK70 = 1;
      if ((int )C_1_st == 0) { BLOCK71 = 1;
        __retres1 = 1;
        goto return_label;
      } else { BLOCK72 = 1;

      }
    }
  }
  __retres1 = 0;
  return_label: /* CIL Label */ 
  return (__retres1);
}
}
void eval(void) 
{ int tmp ;
  int tmp___0 ;
  int tmp___1 ;
  int tmp___2 ;
  BLOCK73 = 1;
//  int __VERIFIER_nondet_int();

  {
  {
  while (1) {   BLOCK74 = 1;
    while_3_continue: /* CIL Label */ ;
    {
    tmp___2 = exists_runnable_thread();
    }
    if (tmp___2) { BLOCK75 = 1;

    } else { BLOCK76 = 1;
      goto while_3_break;
    }
    if ((int )P_1_st == 0) { BLOCK77 = 1;
      {
      tmp = __VERIFIER_nondet_int();
      }
      if (tmp) { BLOCK78 = 1;
        {
        P_1_st = 1;
        P_1();
        }
      } else { BLOCK79 = 1;

      }
    } else { BLOCK80 = 1;

    }
    if ((int )P_2_st == 0) { BLOCK81 = 1;
      {
      tmp___0 = __VERIFIER_nondet_int();
      }
      if (tmp___0) { BLOCK82 = 1;
        {
        P_2_st = 1;
        P_2();
        }
      } else { BLOCK83 = 1;

      }
    } else { BLOCK84 = 1;

    }
    if ((int )C_1_st == 0) { BLOCK85 = 1;
      {
	tmp___1 = __VERIFIER_nondet_int();
      }
      if (tmp___1) { BLOCK86 = 1;
        {
        C_1_st = 1;
        C_1();
        }
      } else { BLOCK87 = 1;

      }
    } else { BLOCK88 = 1;

    }
  }
  while_3_break: /* CIL Label */ ;
  }

  return;
}
}
void fire_delta_events(void) 
{ 

  BLOCK89 = 1;

  return;

}
void reset_delta_events(void) 
{ 

  BLOCK90 = 1;

  return;

}
void fire_time_events(void) 
{ 
  BLOCK91 = 1;  // BUG 1/1, should be the body of a conditional statement. 
  C_1_ev = 1;
  P_1_ev = 1;
  P_2_ev = 1;

  return;

}
void reset_time_events(void) 
{ 
  BLOCK92 = 1;
  {
  if ((int )P_1_ev == 1) { BLOCK93 = 1;
    P_1_ev = 2;
  } else { BLOCK94 = 1;

  }
  if ((int )P_2_ev == 1) { BLOCK95 = 1;
    P_2_ev = 2;
  } else { BLOCK96 = 1;

  }
  if ((int )C_1_ev == 1) { BLOCK97 = 1;
    C_1_ev = 2;
  } else { BLOCK98 = 1;

  }

  return;
}
}
void activate_threads(void) 
{ int tmp ;
  int tmp___0 ;
  int tmp___1 ;
BLOCK99 = 1;
  {
  {
  tmp = is_P_1_triggered();
  }
  if (tmp) { BLOCK100 = 1;
    P_1_st = 0;
  } else {  BLOCK101 = 1;

  }
  {
  tmp___0 = is_P_2_triggered();
  }
  if (tmp___0) { BLOCK102 = 1;
    P_2_st = 0;
  } else { BLOCK103 = 1;

  }
  {
  tmp___1 = is_C_1_triggered();
  }
  if (tmp___1) { BLOCK104 = 1;
    C_1_st = 0;
  } else { BLOCK105 = 1;

  }

  return;
}
}
void immediate_notify(void) 
{  BLOCK106 = 1;



  activate_threads();


  return;

}
int stop_simulation(void) 
{ int tmp ;
  int __retres2 ;
  BLOCK107 = 1;
  {
  {
  tmp = exists_runnable_thread();
  }
  if (tmp) { BLOCK108 = 1;
    __retres2 = 0;
    goto return_label;
  } else { BLOCK109 = 1;

  }
  __retres2 = 1;
  return_label: /* CIL Label */ 
  return (__retres2);
}
}
void start_simulation(void) 
{ int kernel_st ;
  int tmp ;
  int tmp___0 ;
  BLOCK110 = 1;
  {
  {
  kernel_st = 0;
  update_channels();
  init_threads();
  fire_delta_events();
  activate_threads();
  reset_delta_events();
  }
  {
  while (1) { BLOCK111 = 1;
    while_4_continue: /* CIL Label */ ;
    {
    kernel_st = 1;
    eval();
    }
    {
    kernel_st = 2;
    update_channels();
    }
    {
    kernel_st = 3;
    fire_delta_events();
    activate_threads();
    reset_delta_events();
    }
    {
    tmp = exists_runnable_thread();
    }
    if (tmp == 0) { BLOCK112 = 1;
      //{
      kernel_st = 4;
      fire_time_events();
      activate_threads();
      reset_time_events();
      //}
    } else { BLOCK113= 1;

    }
    {
    tmp___0 = stop_simulation();
    }
    if (tmp___0) { BLOCK114 = 1;
      goto while_4_break;
    } else  { BLOCK115 = 1;

    }
  }
  while_4_break: /* CIL Label */ ;
  }

  return;
}
}
void init_model(void) 
{ 

  { BLOCK116 = 1;
  P_1_i = 1;
  P_2_i = 1;
  C_1_i = 1;

  return;
}
}
int main(void) 
{ int count ;
  int __retres2 ;
  BLOCK117 = 1; 
  {
  {
  num  =    0;
  i  =    0;
  max_loop = 2;
  e  ;
  timer  =    0;
  P_1_pc  =    0;
  P_2_pc  =    0;
  C_1_pc  =    0;

  count = 0;
  init_model();
  start_simulation(); 
  } 
  __retres2 = 0;
  return (__retres2);
}


}



