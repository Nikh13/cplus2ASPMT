:- sorts
maxValues;negativeValues;state.

:- objects
0..40::maxValues;
-50..50::negativeValues;
stopped,running::state.

:- constants
currentState :: inertialFluent(state);
distance :: simpleFluent(maxValues);
speed :: simpleFluent(negativeValues);
acceleration :: simpleFluent(negativeValues);
accelerate :: exogenousAction;
decelerate :: exogenousAction;
startEngine :: exogenousAction;
stop :: exogenousAction;
duration :: exogenousAction(maxValues);
someAction :: action.

:- variables
X :: negativeValues;
X1 :: negativeValues;
X2 :: negativeValues;
D :: maxValues;
D1 ::maxValues;
T :: maxValues;
RP :: maxValues;
R :: negativeValues.

%Sytem Rules
caused duration=0 if accelerate.
caused duration=0 if decelerate.
caused duration=0 if startEngine.
caused duration=0 if stop.

default ~someAction.
caused someAction if accelerate.
caused someAction if decelerate.
caused someAction if startEngine.
caused someAction if stop.


%Flow
caused distance = D after currentState = stopped & distance = D1 & duration = T & D = D1 + 0*T & -(someAction).
caused speed = X after currentState = stopped & speed = X1 & duration = T & X = X1 + 0*T & -(someAction).
caused acceleration = X after currentState = stopped & acceleration = X1 & duration = T & X = X1 + 0*T & -(someAction).

caused distance = D after speed = X1 & acceleration = X2 & currentState = running & distance = D1 & duration = T & D = D1 + (X1+(X2*T))*T & -(someAction).
caused speed = X after acceleration = X2 & currentState = running & speed = X1 & duration = T & X = X1 + X2*T & -(someAction).
caused acceleration = X after currentState = running & acceleration = X1 & duration = T & X = X1 + 0*T & -(someAction).

%Guard
nonexecutable startEngine if -(currentState=stopped).

nonexecutable stop if -(currentState=running).
nonexecutable stop if -(speed=0).

nonexecutable accelerate if -(currentState=running).

nonexecutable decelerate if -(currentState=running).

%Reset
caused distance = RP after startEngine & distance = D & RP=D.
caused speed = R after startEngine & R=0.
caused acceleration = R after startEngine & R=0 .
caused currentState=running after startEngine & currentState=stopped.

caused distance = RP after accelerate & distance = D & RP=D.
caused speed = R after accelerate & speed =X & R=X.
caused acceleration = R after accelerate & acceleration=X & R=X+1.
caused currentState=running after accelerate & currentState=running & duration=0.

caused distance = RP after decelerate & distance = D & RP=D.
caused speed = R after decelerate & speed =X & R=X.
caused acceleration = R after decelerate & acceleration=X & R=X-1.
caused currentState=running after decelerate & currentState=running.

caused distance = RP after stop & distance = D & RP=D.
caused speed = R after stop & R=0.
caused acceleration = R after stop & R=0.
caused currentState=stopped after stop & currentState=running.

:- query
label :: init;
maxstep :: 7;
0:distance=0;
0:speed=0;
0:acceleration=0;
0:currentState = stopped;
0:startEngine;
1:accelerate;
2: --(duration=2);
7: --(currentState=stopped).
