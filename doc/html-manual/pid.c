// CONSTANTS:
#define MAX_CLIMB_SUM_ERR 100
#define MAX_CLIMB 1

#define CLOCK 16
#define MAX_PPRZ (CLOCK*600)

#define CLIMB_LEVEL_GAZ 0.31
#define CLIMB_GAZ_OF_CLIMB 0.75
#define CLIMB_PITCH_OF_VZ_PGAIN 0.05
#define CLIMB_PGAIN -0.03
#define CLIMB_IGAIN 0.1

const float pitch_of_vz_pgain=CLIMB_PITCH_OF_VZ_PGAIN;
const float climb_pgain=CLIMB_PGAIN;
const float climb_igain=CLIMB_IGAIN;
const float nav_pitch=0;

// 1) the target speed in vertical direction
float desired_climb;
// 2) vertical speed of the UAV detected by GPS sensor
float estimator_z_dot;

/** PID funciton OUTPUTS */
float desired_gaz;
float desired_pitch;
// Accumulated error in the system
float climb_sum_err;


/** Computes desired_gaz and desired_pitch */
void climb_pid_run() 
{

  float err=estimator_z_dot-desired_climb;

  float fgaz=climb_pgain*(err+climb_igain*climb_sum_err)+CLIMB_LEVEL_GAZ+CLIMB_GAZ_OF_CLIMB*desired_climb;

  float pprz=fgaz*MAX_PPRZ;
  desired_gaz=((pprz>=0 && pprz<=MAX_PPRZ) ? pprz : (pprz>MAX_PPRZ ? MAX_PPRZ : 0));
  
  /** pitch offset for climb */
  float pitch_of_vz=(desired_climb>0) ? desired_climb*pitch_of_vz_pgain : 0;
  desired_pitch=nav_pitch+pitch_of_vz;

  climb_sum_err=err+climb_sum_err;
  if (climb_sum_err>MAX_CLIMB_SUM_ERR) climb_sum_err=MAX_CLIMB_SUM_ERR;
  if (climb_sum_err<-MAX_CLIMB_SUM_ERR) climb_sum_err=-MAX_CLIMB_SUM_ERR;

  /** The control function for estimating the vertical speed */
  estimator_z_dot=climb_pgain * err + desired_climb;

}


int main()
{
  /** Non-deterministic initialisation */ 
  desired_climb=nondet_float();
  estimator_z_dot=nondet_float();

  /** Range of initial values of variables */ 
  __CPROVER_assume(desired_climb>=-MAX_CLIMB && desired_climb<=MAX_CLIMB);
  __CPROVER_assume(estimator_z_dot>=-MAX_CLIMB && estimator_z_dot<=MAX_CLIMB);

  while(1)
  {
    climb_pid_run(); 
  }

  return 0;
}

