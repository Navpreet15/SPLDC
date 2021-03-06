// BASIC DEFINITIONS
abstract sig Feature{}

one sig EmergencyAlarm, MultipleElevators, Timers, Sensors, FloorButtons, 
ElevatorButtons extends Feature{}

// FEATURE MODEL DEFINITION
abstract sig FeatureModel{
	feature: some Feature
}

fact {all f: FeatureModel | Timers in f.feature}
fact {all f: FeatureModel | FloorButtons in f.feature}
fact {all f: FeatureModel | ElevatorButtons in f.feature}
fact {all f: FeatureModel | Sensors in f.feature}

//Domain Model Definition
abstract sig Interface{}
one sig OutputDeviceInterface, InputDeviceInterface, StateDependentControl, Timer, 
Coordinator, Server, Entity, Alarm extends Interface{}

abstract sig Class{
interface: lone Interface,
}
one sig DoorInterface, ElevatorLampInterface, MotorInterface, ElevatorButtonInterface,
ArrivalSensorInterface, ElevatorControl, DoorTimer, WeightSensorInterface, 
ElevatorStatusandPlan, DirectionLampInterface, FloorButtonInterface, FloorLampInterface,
ElevatorStatusandPlanServer, OverallElevatorStatusandPlan, ElevatorScheduler,
EmergencyAlarmInterface, ElevatorManager extends Class{}

//abstract sig Attribute{}
//one sig Illuminated, label extends Attribute{}
//Defining boolean datatype
abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

one sig HelpButton extends Class{
Illuminated: Bool,
label: String }


fact{HelpButton.Illuminated = True and HelpButton.label = "HELP"}
fact {DoorInterface.interface = OutputDeviceInterface}
fact {ElevatorLampInterface.interface = OutputDeviceInterface}
fact {MotorInterface.interface = OutputDeviceInterface}
fact {ElevatorButtonInterface.interface = InputDeviceInterface}
fact {ArrivalSensorInterface.interface = InputDeviceInterface}
fact {ElevatorControl.interface = StateDependentControl}
fact {DoorTimer.interface = Timer}
fact {WeightSensorInterface.interface = InputDeviceInterface}
fact {ElevatorStatusandPlan.interface = Entity}
fact {DirectionLampInterface.interface = OutputDeviceInterface}
fact {FloorButtonInterface.interface = InputDeviceInterface}
fact {FloorLampInterface.interface = OutputDeviceInterface}
fact {ElevatorStatusandPlanServer.interface = Server}
fact {OverallElevatorStatusandPlan.interface = Entity}
fact {ElevatorScheduler.interface = Coordinator}
fact {EmergencyAlarmInterface.interface = Alarm}



abstract sig Label{}
one sig Controls, Requests, Notifies, Updates, Selects, Checks, Commands,
Extend extends Label{}


abstract sig Relationship{
from: one Class,
to: one Class,
label: one Label,
inMul:one Int,
outMul: one Int}

one sig R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, 
R14, R15, R16, R17, R18, R19 extends Relationship{}

fact{R1.from = ElevatorControl and R1.to= DoorInterface and R1.label=Controls and
R1.inMul=1 and R1.outMul=1}

fact{R2.from = ElevatorControl and R2.to= ElevatorLampInterface and R2.label=Controls and
R2.inMul=1 and R2.outMul=1}

fact{R3.from = ElevatorControl and R3.to= MotorInterface and R3.label=Controls and
R3.inMul=1 and R3.outMul=1}

fact{R4.from = ArrivalSensorInterface and R4.to= ElevatorControl and R4.label=Notifies and
R4.inMul=1 and R4.outMul >= 1}

fact{R5.from = DoorTimer and R5.to= ElevatorControl and R5.label=Notifies and
R5.inMul=1 and R5.outMul=1 }

fact{R6.from = WeightSensorInterface and R6.to= ElevatorControl and R6.label=Notifies and
R6.inMul=1 and R6.outMul=1 }

fact{R7.to = ElevatorStatusandPlan and R7.from= ElevatorControl and R7.label=Checks and
R7.inMul=1 and R7.outMul=1 }

fact{R8.from = ElevatorManager and R8.to= ElevatorControl and R8.label=Commands and
R8.inMul=1 and R8.outMul=1 }

fact{R9.from = ElevatorManager and R9.to= ElevatorStatusandPlan and R9.label=Updates and
R9.inMul=1 and R9.outMul=1 }

fact{R10.to = DirectionLampInterface and R10.from= ElevatorControl and R10.label=Controls and
R10.inMul >=1 and R10.outMul=1 }

fact{R11.from = ElevatorControl and R11.to= FloorLampInterface and R11.label=Controls and
R11.inMul >=1 and R11.outMul >=1 }

fact{R12.from = FloorButtonInterface and R12.to= ElevatorScheduler and R12.label=Requests and
R12.inMul =1 and R12.outMul>=1 }

fact{R13.from = ElevatorManager and R13.to= ElevatorStatusandPlanServer and R13.label=Updates and
R13.inMul >=1 and R13.outMul=1 }

fact{R14.from = ElevatorStatusandPlanServer and R14.to= OverallElevatorStatusandPlan and R14.label=Updates and
R14.inMul=1 and R14.outMul=1 }

fact{R15.from = ElevatorScheduler and R15.to= ElevatorManager and R15.label=Requests and
R15.inMul=1 and R15.outMul >=1 }

fact{R16.from = ElevatorScheduler and R16.to= OverallElevatorStatusandPlan and R16.label=Selects and
R16.inMul=1 and R16.outMul=1 }

fact{R17.from = ElevatorButtonInterface and R17.to= ElevatorManager and R17.label=Requests and
R17.inMul=1 and R17.outMul >=1 }

fact{R18.from = EmergencyAlarmInterface and R18.to= ElevatorControl and R18.label= Notifies and
R18.inMul=1 and R18.outMul =1 }

fact{R19.from = HelpButton and R19.to= ElevatorButtonInterface and R19.label= Extend and
R19.inMul=1 and R19.outMul =1 }

abstract sig ClassDiagram{
class : some Class,
relationship: some Relationship
}

//List all the actions
abstract sig Entry{}
one sig UpdateIdleStatus, CloseDoor, OffUpFloorLamp, OffDownFloorLamp, Departed,
 CommunicationChannelActive, HELPButtonOn, 
EmergencyPowerButtonOn extends Entry{}


abstract sig State{
entry : set Entry}
one sig ElevatorIdle, DoorClosingToMoveUp, DoorClosingToMoveDown, ElevatorStartingUp,
ElevatorStartingDown, ElevatorMoving, ElevatorStopping, ElevatorDoorOpening,
ElevatorAtFloor, CheckingNextDestination, EmergencyMode,
DoorClosingToMoveup, DoorClosingToMovedown extends State{}



//List all the guards
abstract sig Trigger{}
one sig UpRequest, DownRequest, DoorClosed, ApproachingFloor, 
ApproachingRequestedFloor, ElevatorStopped, DoorOpened, AfterTimeout,
ElevatorStarted, NoRequest, PowerFailure extends Trigger{}

abstract sig TransitionBehavior{}
one sig Up, OffUpDirectionLamp, Down, OffDownDirectionLamp, CheckThisFloor, Stop,
OnDirectionLamp, DoorOpen, StartTimer,
 CheckNextDestination, Arrived, OffElevatorLamp,
EmergencyAlarmRinging extends TransitionBehavior{}

abstract sig Transition{
to: one State,
from: one State,
trigger: some Trigger,
tb : set TransitionBehavior
}
one sig T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14,
T15, T16, T17, T18, T19 extends Transition{}

abstract sig StateChart{
state: some State,
transition : some Transition}

fact {ElevatorIdle.entry = UpdateIdleStatus}
fact{ElevatorMoving.entry = Departed}
fact {EmergencyMode.entry = (CommunicationChannelActive + HELPButtonOn + 
EmergencyPowerButtonOn)}


//Entries Depending on th Design Choices
fact {DoorClosingToMoveUp.entry = {CloseDoor + OffUpFloorLamp}}
fact {DoorClosingToMoveDown.entry = {CloseDoor + OffDownFloorLamp}}

fact{T1.from = ElevatorIdle and T1.to = DoorClosingToMoveUp and T1.trigger = UpRequest
and T1.tb = none }

fact{T2.from = ElevatorIdle and T2.to = DoorClosingToMoveDown and 
T2.trigger = DownRequest and T1.tb = none }

fact{T3.from = DoorClosingToMoveUp and T3.to = ElevatorStartingUp and
 T3.trigger = DoorClosed and T3.tb = {Up}}

fact{T15.from = DoorClosingToMoveUp and T15.to = ElevatorStartingUp and
 T15.trigger = DoorClosed and T15.tb = {Up + OffUpDirectionLamp}}

fact{T4.from = DoorClosingToMoveDown and T4.to = ElevatorStartingDown and
 T4.trigger = DoorClosed and T4.tb = {Down} }


fact{T16.from = DoorClosingToMoveDown and T16.to = ElevatorStartingDown and
 T16.trigger = DoorClosed and T16.tb = {Down + OffDownDirectionLamp} }


fact{T5.from = ElevatorStartingUp and T5.to = ElevatorMoving and
 T5.trigger = ElevatorStarted and T5.tb = none }

fact{T6.from = ElevatorStartingDown and T6.to = ElevatorMoving and
 T6.trigger = ElevatorStarted and T6.tb = none }

fact{T7.from = ElevatorMoving and T7.to = ElevatorMoving and
 T7.trigger = ApproachingFloor and T7.tb = CheckThisFloor }

fact{T8.from = ElevatorMoving and T8.to = ElevatorStopping and
 T8.trigger = ApproachingRequestedFloor and T8.tb = {Stop} }


fact{T17.from = ElevatorMoving and T17.to = ElevatorStopping and
 T17.trigger = ApproachingRequestedFloor and T17.tb = {Stop + OnDirectionLamp} }


fact{T9.from = ElevatorStopping and T9.to = ElevatorDoorOpening and
 T9.trigger = ElevatorStopped and T9.tb = {DoorOpen + Arrived}}

fact{T18.from = ElevatorStopping and T18.to = ElevatorDoorOpening and
 T18.trigger = ElevatorStopped and T18.tb = {DoorOpen + OffElevatorLamp + Arrived}}



fact{T10.from = ElevatorDoorOpening and T10.to = ElevatorAtFloor and
 T10.trigger = DoorOpened and T10.tb = StartTimer }

fact{T11.from = ElevatorAtFloor and T11.to = CheckingNextDestination and
 T11.trigger = AfterTimeout and T11.tb= CheckNextDestination }

fact{T12.from = CheckingNextDestination and T12.to = ElevatorIdle and
 T12.trigger = NoRequest and T12.tb = none }

fact{T13.from = CheckingNextDestination and T13.to = DoorClosingToMoveUp and
 T13.trigger = UpRequest and T13.tb = none }

fact{T14.from = CheckingNextDestination and T14.to = DoorClosingToMoveDown and
 T14.trigger = DownRequest and T14.tb = none }

fact {T19.from=ElevatorMoving and T19.to = EmergencyMode and 
T19.trigger = PowerFailure and T19.tb = EmergencyAlarmRinging}



fact{all s : StateChart | T1 in s.transition}
fact{all s : StateChart | T2 in s.transition}
fact{all s : StateChart | T5 in s.transition}
fact{all s : StateChart | T6 in s.transition}
fact{all s : StateChart | T7 in s.transition}
fact{all s : StateChart | T10 in s.transition}
fact{all s : StateChart | T11 in s.transition}
fact{all s : StateChart | T12 in s.transition}
fact{all s : StateChart | T13 in s.transition}
fact{all s : StateChart | T14 in s.transition}



abstract sig DomainModel{
cd : one ClassDiagram,
sc: one StateChart
}


//Always True about DomainModel
fact {all d: ClassDiagram | (R1 in d.relationship) and (R3 in  d.relationship) and 
(R7  in d.relationship) and (R8  in d.relationship) and (R9  in d.relationship)and
 (R13  in d.relationship) and ( R14  in d.relationship)
}

// Metamodel well-formedness constraints
fact {
	all d: ClassDiagram | all r: Relationship | r in d.relationship => 
	(r.from in d.class) and (r.to in d.class)
}


//Product Definition
abstract sig Product{
dm: one DomainModel,
config: one FeatureModel}

//Well formdness rules
fact{all f: FeatureModel | f in Product.config}
fact{all d: DomainModel | d in Product.dm}
one sig F1, F2 extends FeatureModel{}

//Product line definition
abstract sig SPL{
product : some Product
}

fact {all p: Product | p in SPL.product}


//Feature Mapping
fact { all p: Product  | 
Timers in p.config.feature => R5 in p.dm.cd.relationship}

fact {all p: Product |
EmergencyAlarm in p.config.feature => R18 in p.dm.cd.relationship}

fact {all p: Product |
FloorButtons in p.config.feature => R12 in p.dm.cd.relationship}

fact {all p: Product |
ElevatorButtons in p.config.feature => R17 in p.dm.cd.relationship}

fact {all p: Product | 
Sensors in p.config.feature => R4 in p.dm.cd.relationship}

fact {all p: Product | 
MultipleElevators in p.config.feature =>
 ((R15 in p.dm.cd.relationship) and (R16 in p.dm.cd.relationship))}

//SPLDCs
//Choices
abstract sig Choice{}
one sig WeightSensor, IlluminatingLamps, DirectionIndication,
 EmergencyHandling extends Choice{}

//ChoiceModel definition
abstract sig ChoiceModel{
choice : set Choice}

//Design Choices Definition
abstract sig DesignChoices{
cm : one ChoiceModel,
spl : one SPL
}

fact {all c: ChoiceModel | c in DesignChoices.cm}
fact{all s: SPL | s in DesignChoices.spl}

//spldc definition
one sig SPLDC{
dc : some DesignChoices
}

fact {all d: DesignChoices | d in SPLDC.dc}

//Decision Mapping
fact {all dec: DesignChoices | all s: dec.spl | all p: s.product |
 WeightSensor in dec.cm.choice =>
WeightSensorInterface in p.dm.cd.class
else WeightSensorInterface not in p.dm.cd.class }

fact {all dec: DesignChoices | all s: dec.spl | all p: s.product |
IlluminatingLamps in dec.cm.choice =>
((R2 in p.dm.cd.relationship) and (R10 in p.dm.cd.relationship)
and (R11 in p.dm.cd.relationship))
else ((R2 not in p.dm.cd.relationship) and (R10 not in p.dm.cd.relationship)
and (R11 not in p.dm.cd.relationship))
}


fact{all dec: DesignChoices | all s: dec.spl | all p: s.product |
 EmergencyHandling in dec.cm.choice=>
((R18 in p.dm.cd.relationship) and (R19 in p.dm.cd.relationship))
else ((R18 not in p.dm.cd.relationship) and (R19 not in p.dm.cd.relationship))}


//decision mapping from design choices to stateChart
fact {all dec: DesignChoices | all s: dec.spl | all p: s.product | all d : p.dm | all s : d.sc | 
IlluminatingLamps in dec.cm.choice => 
((T15 in s.transition) and (T3 not in s.transition))
else ((T15 not in s.transition) and (T3 in s.transition))}

fact {all dec: DesignChoices | all s: dec.spl | all p: s.product | all d : p.dm | all s : d.sc | 
IlluminatingLamps in dec.cm.choice => 
((T16 in s.transition) and (T4 not in s.transition))
else ((T16 not in s.transition) and (T4 in s.transition))}

fact {all dec: DesignChoices | all s: dec.spl | all p: s.product | all d : p.dm | all s : d.sc | 
(IlluminatingLamps in dec.cm.choice) and (DirectionIndication in dec.cm.choice) => 
((T17 in s.transition) and (T8 not in s.transition))
else ((T17 not in s.transition) and (T8 in s.transition))}

fact {all dec: DesignChoices | all s: dec.spl | all p: s.product | all d : p.dm | all s : d.sc | 
(IlluminatingLamps in dec.cm.choice) => 
((T18 in s.transition) and (T9 not in s.transition))
else ((T18 not in s.transition) and (T9 in s.transition))}




//symmetry breaking constraints
fact {all c1, c2 : ClassDiagram | c1.relationship = c2.relationship => c1 = c2}
fact {all s1, s2 : StateChart | (s1.state = s2.state) and (s1.transition = s2.transition)
=> s1=s2 }
fact {all f1, f2 : FeatureModel | f1.feature = f2.feature => f1= f2}
fact {all d1, d2 : DomainModel | (d1.cd = d2.cd) and (d1.sc = d2.sc) => d1=d2}
fact {all t1, t2 : Relationship | (t1.from = t2.from) and (t1.to = t2.to) =>
t1=t2}
fact {all p1, p2 : Product | (p1.config = p2.config) and (p1.dm=p2.dm)=>
p1 = p2}

fact{all c1, c2 : ChoiceModel | c1.choice = c2.choice =>
c1 = c2}
fact {all dc1, dc2 : DesignChoices | dc1.cm = dc2.cm =>
dc1=dc2}

pred model{}
run model for 10




// All o/p devices are controlled by elevator control
//For All For All

assert controlling { all pl: SPL | all p: pl.product | 
all r : p.dm.cd.relationship | ((r.label = Controls) and (r.to.interface= OutputDeviceInterface)) => r.from = ElevatorControl
  }

// There is no class related to itself
assert self { all pl: SPL | all p: pl.product | 
all r : p.dm.cd.relationship | (r.to != r.from)
  }

// there is no direct relation between input device and output device interface
assert direct { all pl: SPL | all p: pl.product | 
no r : p.dm.cd.relationship | (r.to.interface= InputDeviceInterface and  
r.from.interface = OutputDeviceInterface)
  }

// Gives product as counterexample
assert sch {all pl: SPL | all p: pl.product |  
all c : p.dm.cd.class | ElevatorScheduler in c
  }

//for all exist
assert schexist {all pl: SPL | some p: pl.product |  
ElevatorScheduler in p.dm.cd.class
  }

assert R18exist {all pl: SPL | some p: pl.product |  
R18 in p.dm.cd.relationship
  }

//exist for all
assert schexist1 {some pl: SPL | all p: pl.product |  
R15 in p.dm.cd.relationship
  }


//HELP_Button assurance cases
//Case 1: Help button always present in domain model
assert HelpbuttonNA {all pl: SPL | all p: pl.product |all d: p.dm | R19 in d.cd.relationship}
assert HelpbuttonNS{all pl:SPL | some p: pl.product |all d: p.dm| R19 in d.cd.relationship}
assert HelpbuttonPA{some pl:SPL | all p: pl.product |all d: p.dm | R19 in d.cd.relationship}
assert HelpbuttonPS{some pl:SPL | some p: pl.product |all d: p.dm | R19 in d.cd.relationship}


//Case 2: Helpbutton is always illuminated
assert HelpbuttonIlluminatedNA {all pl: SPL | all p: pl.product |all d: p.dm | HelpButton.Illuminated = True}

//Case 3: Help button labeled as HELP
assert HelpbuttonlabelNA {all pl: SPL | all p: pl.product |all d: p.dm | HelpButton.label = "HELP"}


// Two way communication provided in emergency
assert CommunicationChannelNA{all pl: SPL | all p: pl.product | all d: p.dm | 
CommunicationChannelActive in EmergencyMode.entry }

//Emergency mode state always present in the state chart




//InitialStateNA
assert initialStateNA {all pl: SPL | all p: pl.product| some s: p.dm.sc.state | 
(s in p.dm.sc.transition.from) and (s not in  p.dm.sc.transition.to)}

assert finalState {all pl: SPL | all p: pl.product| some s: p.dm.state | 
(s not in p.dm.sc.transition.source) and (s in  p.dm.sc.transition.target)}





check controlling for 20
check self for 20
check direct for 20
check sch for 20
check schexist for 20
check R18exist for 20
check schexist1 for 20
check HelpbuttonNA for 10
check HelpbuttonNS for 10
check HelpbuttonPA for 10
check HelpbuttonPS for 10
check HelpbuttonIlluminatedNA for 10
check  HelpbuttonlabelNA for 10
check CommunicationChannelNA for 10
check initialStateNA for 10
