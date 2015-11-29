
#define TIMEOUT1 4  //400
#define TIMEOUT2 6  //600
#define TIMEOUT3 10 //5400

/* Named Constants */

#define FALSE 0
#define TRUE 1

/* Type declarations */

typedef char INT8;

typedef unsigned char UINT8;

typedef short INT16;

typedef unsigned short UINT16;

typedef int INT32;

typedef unsigned int UINT32;

typedef double REAL;

typedef float SINGLE;

typedef unsigned char BOOL;


/* Function-like macros */

/*  Conversion to the BOOL type  */
#define TO_BOOL(X) ((X) ? 1 : 0)

/* Type declarations */

typedef struct {
    INT32 Counter;
    BOOL InitSystem_OPEN;
    BOOL VehicleOpen_OPEN;
    BOOL AlarmWillBeArmedAfter20sec_CounterStart_OPEN;
    BOOL AlarmWillBeArmedAfter20sec_CounterPlus_OPEN;
    BOOL AlarmWillBeArmedAfter20sec_CounterEnd_OPEN;
    BOOL AlarmWillBeArmedAfter20sec_OPEN;
    BOOL AlarmOnlyOptical_CounterPlus_OPEN;
    BOOL AlarmOnlyOptical_CounterStart_OPEN;
    BOOL AlarmOnlyOptical_CounterEnd_OPEN;
    BOOL AlarmOnlyOptical_OPEN;
    BOOL AlarmAcousticAndOptical_CounterStart_OPEN;
    BOOL AlarmAcousticAndOptical_CounterPlus_OPEN;
    BOOL AlarmAcousticAndOptical_CounterEnd_OPEN;
    BOOL AlarmAcousticAndOptical_OPEN;
    BOOL AlarmArmed_OPEN;
    BOOL Alarm_system_OPEN;
} t_Alarm_system_state;

typedef struct {
    BOOL OpticalAlarm;
    BOOL AlarmSensor;
    BOOL VehLocked;
    BOOL AcousticAlarm;
    BOOL AlarmArmed;
} t_Alarm_system_io;

/* Named Constants */

#define ALARM_SYSTEM_TICK 0

void Alarm_system_init(t_Alarm_system_io *_io_, t_Alarm_system_state *_state_) {
    _io_->OpticalAlarm = FALSE;
    _io_->AlarmSensor = FALSE;
    _io_->VehLocked = FALSE;
    _io_->AcousticAlarm = FALSE;
    _io_->AlarmArmed = FALSE;
    _state_->Counter = 0;
    _state_->InitSystem_OPEN = 0;
    _state_->VehicleOpen_OPEN = 0;
    _state_->AlarmWillBeArmedAfter20sec_CounterStart_OPEN = 0;
    _state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN = 0;
    _state_->AlarmWillBeArmedAfter20sec_CounterEnd_OPEN = 0;
    _state_->AlarmWillBeArmedAfter20sec_OPEN = 0;
    _state_->AlarmOnlyOptical_CounterPlus_OPEN = 0;
    _state_->AlarmOnlyOptical_CounterStart_OPEN = 0;
    _state_->AlarmOnlyOptical_CounterEnd_OPEN = 0;
    _state_->AlarmOnlyOptical_OPEN = 0;
    _state_->AlarmAcousticAndOptical_CounterStart_OPEN = 0;
    _state_->AlarmAcousticAndOptical_CounterPlus_OPEN = 0;
    _state_->AlarmAcousticAndOptical_CounterEnd_OPEN = 0;
    _state_->AlarmAcousticAndOptical_OPEN = 0;
    _state_->AlarmArmed_OPEN = 0;
    _state_->Alarm_system_OPEN = 0;
}

void Alarm_system_compute(t_Alarm_system_io *_io_, t_Alarm_system_state *_state_) {
    UINT16 activeEvent = ALARM_SYSTEM_TICK;
    if (!_state_->Alarm_system_OPEN) {
        /*  Open the chart  */
        _state_->Alarm_system_OPEN = TRUE;
        /*  Enter the chart's composition  */
        /*  Enter state InitSystem  */
        _state_->InitSystem_OPEN = TRUE;
    } else {
        /*  Execute an open chart  */
        if (_state_->InitSystem_OPEN) {
            /*  Execute state InitSystem  */
            if (_io_->VehLocked == 1) {
                _state_->InitSystem_OPEN = FALSE;
                _state_->AlarmWillBeArmedAfter20sec_OPEN = TRUE;
                /*  Open the inner composition of state AlarmWillBeArmedAfter20sec  */
                /*  Enter state AlarmWillBeArmedAfter20sec.CounterStart  */
                _state_->AlarmWillBeArmedAfter20sec_CounterStart_OPEN = TRUE;
                /*  Perform entry actions of state AlarmWillBeArmedAfter20sec.CounterStart  */
                _state_->Counter = 1;
            } else {
                if (_io_->VehLocked == 0) {
                    _state_->InitSystem_OPEN = FALSE;
                    _state_->VehicleOpen_OPEN = TRUE; //possible BUG 
                } else {
                    /*  Perform during and on-event actions of state InitSystem  */
                    _io_->AlarmArmed = TO_BOOL(1);
                    _io_->AcousticAlarm = TO_BOOL(0);
                    _io_->OpticalAlarm = TO_BOOL(0);
                }
            }
        } else {
            if (_state_->VehicleOpen_OPEN) {
                /*  Execute state VehicleOpen  */
                if (_io_->VehLocked == 1) {
                    _state_->VehicleOpen_OPEN = FALSE;
                    _state_->AlarmWillBeArmedAfter20sec_OPEN = TRUE;
                    /*  Open the inner composition of state AlarmWillBeArmedAfter20sec  */
                    /*  Enter state AlarmWillBeArmedAfter20sec.CounterStart  */
                    _state_->AlarmWillBeArmedAfter20sec_CounterStart_OPEN = TRUE;
                    /*  Perform entry actions of state AlarmWillBeArmedAfter20sec.CounterStart  */
                    _state_->Counter = 1;
                } else {
                    /*  Perform during and on-event actions of state VehicleOpen  */
                    _io_->AlarmArmed = TO_BOOL(0);
                    _io_->AcousticAlarm = TO_BOOL(0);
                    _io_->OpticalAlarm = TO_BOOL(0);
                }
            } else {
                if (_state_->AlarmWillBeArmedAfter20sec_OPEN) {
                    /*  Execute state AlarmWillBeArmedAfter20sec  */
                    if (_state_->Counter == 0 && _io_->VehLocked == 1) {
                        /*  Close the inner composition of state AlarmWillBeArmedAfter20sec  */
                        if (_state_->AlarmWillBeArmedAfter20sec_CounterStart_OPEN) {
                            _state_->AlarmWillBeArmedAfter20sec_CounterStart_OPEN = FALSE;
                        } else {
                            if (_state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN) {
                                _state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN = FALSE;
                            } else {
                                if (_state_->AlarmWillBeArmedAfter20sec_CounterEnd_OPEN) {
                                    _state_->AlarmWillBeArmedAfter20sec_CounterEnd_OPEN = FALSE;
                                }
                            }
                        }
                        _state_->AlarmWillBeArmedAfter20sec_OPEN = FALSE;
                        _state_->AlarmArmed_OPEN = TRUE;
                    } else {
                        if (_io_->VehLocked == 0) {
                            /*  Close the inner composition of state AlarmWillBeArmedAfter20sec  */
                            if (_state_->AlarmWillBeArmedAfter20sec_CounterStart_OPEN) {
                                _state_->AlarmWillBeArmedAfter20sec_CounterStart_OPEN = FALSE;
                            } else {
                                if (_state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN) {
                                    _state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN = FALSE;
                                } else {
                                    if (_state_->AlarmWillBeArmedAfter20sec_CounterEnd_OPEN) {
                                        _state_->AlarmWillBeArmedAfter20sec_CounterEnd_OPEN = FALSE;
                                    }
                                }
                            }
                            _state_->AlarmWillBeArmedAfter20sec_OPEN = FALSE;
			    _state_->VehicleOpen_OPEN = TRUE; //possible BUG
                        } else {
                            /*  Perform during and on-event actions of state AlarmWillBeArmedAfter20sec  */
                            _io_->AlarmArmed = TO_BOOL(0);
                            _io_->AcousticAlarm = TO_BOOL(0);
                            _io_->OpticalAlarm = TO_BOOL(0);
                            if (_state_->AlarmWillBeArmedAfter20sec_CounterStart_OPEN) {
                                /*  Execute state AlarmWillBeArmedAfter20sec.CounterStart  */
                                _state_->AlarmWillBeArmedAfter20sec_CounterStart_OPEN = FALSE;
                                _state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN = TRUE;
                                /*  Perform entry actions of state AlarmWillBeArmedAfter20sec.CounterPlus  */
                                _state_->Counter = _state_->Counter + 1;
                            } else {
                                if (_state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN) {
                                    /*  Execute state AlarmWillBeArmedAfter20sec.CounterPlus  */
                                    if (_state_->Counter < TIMEOUT1 || _io_->VehLocked == 0) {
                                        _state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN = FALSE;
                                        _state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN = TRUE;
                                        /*  Perform entry actions of state AlarmWillBeArmedAfter20sec.CounterPlus  */
                                        _state_->Counter = _state_->Counter + 1;
                                    } else {
                                        _state_->AlarmWillBeArmedAfter20sec_CounterPlus_OPEN = FALSE;
                                        _state_->AlarmWillBeArmedAfter20sec_CounterEnd_OPEN = TRUE;
                                        /*  Perform entry actions of state AlarmWillBeArmedAfter20sec.CounterEnd  */
                                        _state_->Counter = 0;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    if (_state_->AlarmOnlyOptical_OPEN) {
                        /*  Execute state AlarmOnlyOptical  */
                        if (_state_->Counter == 0) {
                            /*  Close the inner composition of state AlarmOnlyOptical  */
                            if (_state_->AlarmOnlyOptical_CounterPlus_OPEN) {
                                _state_->AlarmOnlyOptical_CounterPlus_OPEN = FALSE;
                            } else {
                                if (_state_->AlarmOnlyOptical_CounterStart_OPEN) {
                                    _state_->AlarmOnlyOptical_CounterStart_OPEN = FALSE;
                                } else {
                                    if (_state_->AlarmOnlyOptical_CounterEnd_OPEN) {
                                        _state_->AlarmOnlyOptical_CounterEnd_OPEN = FALSE;
                                    }
                                }
                            }
                            _state_->AlarmOnlyOptical_OPEN = FALSE;
                            _state_->AlarmArmed_OPEN = TRUE;
                        } else {
                            if (_io_->VehLocked == 0) {
                                /*  Close the inner composition of state AlarmOnlyOptical  */
                                if (_state_->AlarmOnlyOptical_CounterPlus_OPEN) {
                                    _state_->AlarmOnlyOptical_CounterPlus_OPEN = FALSE;
                                } else {
                                    if (_state_->AlarmOnlyOptical_CounterStart_OPEN) {
                                        _state_->AlarmOnlyOptical_CounterStart_OPEN = FALSE;
                                    } else {
                                        if (_state_->AlarmOnlyOptical_CounterEnd_OPEN) {
                                            _state_->AlarmOnlyOptical_CounterEnd_OPEN = FALSE;
                                        }
                                    }
                                }
                                _state_->AlarmOnlyOptical_OPEN = FALSE;
				_state_->VehicleOpen_OPEN = TRUE; //possible BUG
                            } else {
                                /*  Perform during and on-event actions of state AlarmOnlyOptical  */
                                _io_->AlarmArmed = TO_BOOL(0);
                                _io_->AcousticAlarm = TO_BOOL(0);
                                _io_->OpticalAlarm = TO_BOOL(1);
                                if (_state_->AlarmOnlyOptical_CounterPlus_OPEN) {
                                    /*  Execute state AlarmOnlyOptical.CounterPlus  */
                                    if (_state_->Counter < TIMEOUT3 && _io_->VehLocked == 1) {
                                        _state_->AlarmOnlyOptical_CounterPlus_OPEN = FALSE;
                                        _state_->AlarmOnlyOptical_CounterPlus_OPEN = TRUE;
                                        /*  Perform entry actions of state AlarmOnlyOptical.CounterPlus  */
                                        _state_->Counter = _state_->Counter + 1;
                                    } else {
                                        _state_->AlarmOnlyOptical_CounterPlus_OPEN = FALSE;
                                        _state_->AlarmOnlyOptical_CounterEnd_OPEN = TRUE;
                                        /*  Perform entry actions of state AlarmOnlyOptical.CounterEnd  */
                                        _state_->Counter = 0;
                                    }
                                } else {
                                    if (_state_->AlarmOnlyOptical_CounterStart_OPEN) {
                                        /*  Execute state AlarmOnlyOptical.CounterStart  */
                                        _state_->AlarmOnlyOptical_CounterStart_OPEN = FALSE;
                                        _state_->AlarmOnlyOptical_CounterPlus_OPEN = TRUE;
                                        /*  Perform entry actions of state AlarmOnlyOptical.CounterPlus  */
                                        _state_->Counter = _state_->Counter + 1;
                                    }
                                }
                            }
                        }
                    } else {
                        if (_state_->AlarmAcousticAndOptical_OPEN) {
                            /*  Execute state AlarmAcousticAndOptical  */
                            if (_state_->Counter == 0) {
                                /*  Close the inner composition of state AlarmAcousticAndOptical  */
                                if (_state_->AlarmAcousticAndOptical_CounterStart_OPEN) {
                                    _state_->AlarmAcousticAndOptical_CounterStart_OPEN = FALSE;
                                } else {
                                    if (_state_->AlarmAcousticAndOptical_CounterPlus_OPEN) {
                                        _state_->AlarmAcousticAndOptical_CounterPlus_OPEN = FALSE;
                                    } else {
                                        if (_state_->AlarmAcousticAndOptical_CounterEnd_OPEN) {
                                            _state_->AlarmAcousticAndOptical_CounterEnd_OPEN = FALSE;
                                        }
                                    }
                                }
                                _state_->AlarmAcousticAndOptical_OPEN = FALSE;
                                _state_->AlarmOnlyOptical_OPEN = TRUE;
                                /*  Open the inner composition of state AlarmOnlyOptical  */
                                /*  Enter state AlarmOnlyOptical.CounterStart  */
                                _state_->AlarmOnlyOptical_CounterStart_OPEN = TRUE;
                                /*  Perform entry actions of state AlarmOnlyOptical.CounterStart  */
                                _state_->Counter = 1;
                            } else {
                                if (_io_->VehLocked == 0) {
                                    /*  Close the inner composition of state AlarmAcousticAndOptical  */
                                    if (_state_->AlarmAcousticAndOptical_CounterStart_OPEN) {
                                        _state_->AlarmAcousticAndOptical_CounterStart_OPEN = FALSE;
                                    } else {
                                        if (_state_->AlarmAcousticAndOptical_CounterPlus_OPEN) {
                                            _state_->AlarmAcousticAndOptical_CounterPlus_OPEN = FALSE;
                                        } else {
                                            if (_state_->AlarmAcousticAndOptical_CounterEnd_OPEN) {
                                                _state_->AlarmAcousticAndOptical_CounterEnd_OPEN = FALSE;
                                            }
                                        }
                                    }
                                    _state_->AlarmAcousticAndOptical_OPEN = FALSE;
				    //BUG _state_->VehicleOpen_OPEN = TRUE; //BUG does not work
                                } else {
                                    /*  Perform during and on-event actions of state AlarmAcousticAndOptical  */
                                    _io_->AlarmArmed = TO_BOOL(0);
                                    _io_->AcousticAlarm = TO_BOOL(1);
                                    _io_->OpticalAlarm = TO_BOOL(1);
                                    if (_state_->AlarmAcousticAndOptical_CounterStart_OPEN) {
                                        /*  Execute state AlarmAcousticAndOptical.CounterStart  */
                                        _state_->AlarmAcousticAndOptical_CounterStart_OPEN = FALSE;
                                        _state_->AlarmAcousticAndOptical_CounterPlus_OPEN = TRUE;
                                        /*  Perform entry actions of state AlarmAcousticAndOptical.CounterPlus  */
                                        _state_->Counter = _state_->Counter + 1;
                                    } else {
                                        if (_state_->AlarmAcousticAndOptical_CounterPlus_OPEN) {
                                            /*  Execute state AlarmAcousticAndOptical.CounterPlus  */
                                            if (_state_->Counter < TIMEOUT2 && _io_->VehLocked == 1) {
                                                _state_->AlarmAcousticAndOptical_CounterPlus_OPEN = FALSE;
                                                _state_->AlarmAcousticAndOptical_CounterPlus_OPEN = TRUE;
                                                /*  Perform entry actions of state AlarmAcousticAndOptical.CounterPlus  */
                                                _state_->Counter = _state_->Counter + 1;
                                            } else {
                                                _state_->AlarmAcousticAndOptical_CounterPlus_OPEN = FALSE;
                                                _state_->AlarmAcousticAndOptical_CounterEnd_OPEN = TRUE;
                                                /*  Perform entry actions of state AlarmAcousticAndOptical.CounterEnd  */
                                                _state_->Counter = 0;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            if (_state_->AlarmArmed_OPEN) {
                                /*  Execute state AlarmArmed  */
                                if (_io_->AlarmSensor == 1) {
                                    _state_->AlarmArmed_OPEN = FALSE;
				    _state_->AlarmAcousticAndOptical_OPEN = TRUE; //BUG does not work
                                    /*  Open the inner composition of state AlarmAcousticAndOptical  */
                                    /*  Enter state AlarmAcousticAndOptical.CounterStart  */
                                    _state_->AlarmAcousticAndOptical_CounterStart_OPEN = TRUE;
                                    /*  Perform entry actions of state AlarmAcousticAndOptical.CounterStart  */
                                    _state_->Counter = 1;
                                } else {
                                    if (_io_->VehLocked == 0) {
                                        _state_->AlarmArmed_OPEN = FALSE;
					_state_->VehicleOpen_OPEN = TRUE; //BUG does not work
                                    } else {
                                        /*  Perform during and on-event actions of state AlarmArmed  */
                                        _io_->AlarmArmed = TO_BOOL(1);
                                        _io_->AcousticAlarm = TO_BOOL(0);
                                        _io_->OpticalAlarm = TO_BOOL(0);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

extern int nondet_int();

t_Alarm_system_io havocIO() {
  t_Alarm_system_io _io_;
  _io_.VehLocked = nondet_int();
  _io_.AlarmSensor = nondet_int();
  __CPROVER_assume(0<=_io_.VehLocked && _io_.VehLocked<=1 &&
                   0<=_io_.AlarmSensor && _io_.AlarmSensor<=1);
  return _io_;
}

int main() {
  int k=0;
  t_Alarm_system_state _state_; 
  t_Alarm_system_state _state_old; 
  t_Alarm_system_io _io_;
  Alarm_system_init(&_io_,&_state_);
  while(1) { 
    _state_old = _state_;
    _io_ = havocIO();
    Alarm_system_compute(&_io_,&_state_);
    if(_state_old.AlarmArmed_OPEN && _io_.AlarmSensor) {
      assert(_state_.AlarmAcousticAndOptical_OPEN);
    }
    if(!_state_.InitSystem_OPEN && _state_old.Counter!=0 && !_io_.AlarmSensor && !_io_.VehLocked) assert(_state_.VehicleOpen_OPEN);
  }
  return 0;
}

