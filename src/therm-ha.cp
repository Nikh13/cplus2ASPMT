:- sorts
values;negativeValues;state.

:- objects
0..30 :: values;
-10..10 :: negativeValues;
on,off :: state.

:- constants
temp :: simpleFluent(values);
duration :: exogenousAction(values);
turnOn :: exogenousAction;
turnOff :: exogenousAction;
currentState :: inertialFluent(state).

:- variables
T,T1,T2 :: values;
D :: negativeValues.

%Extra implicit rules
caused duration = 0 if turnOn.
caused duration = 0 if turnOff.

%Invariant
caused false if currentState=on & -(temp<=20).
caused false if currentState=off & -(temp>=19).

%Flow
caused temp = T after D=1 & currentState=on & temp = T1 & duration = T2 & T=T1+D*T2.
caused temp = T after currentState=off & temp = T1 & duration = T2 & T=T1+((-1)*T2).

% Guard
nonexecutable turnOff if -(temp>=20).
nonexecutable turnOff if -(currentState=on). 
nonexecutable turnOn if -(temp<=19).
nonexecutable turnOn if -(currentState=off).

% State tranistion
caused currentState = off after turnOff & currentState = on.
caused currentState = on after turnOn & currentState = off. 
			  
:- query
label :: init;
maxstep :: 5;
0:currentState=on;
0:temp = 15;
2: --(currentState=off);
maxstep: --(currentState=on).