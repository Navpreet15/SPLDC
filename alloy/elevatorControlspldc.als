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
one sig Controls, Requests, Notifies, Updates, Selects, Checks, Commands extends Label{}


abstract sig Relationship{
from: one Class,
to: one Class,
label: one Label,
inMul:one Int,
outMul: one Int}

one sig R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, 
R14, R15, R16, R17, R18 extends Relationship{}

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
R17.inMul=1 and R17.outMul =1 }

abstract sig DomainModel{
class : some Class,
relationship: some Relationship
}
//Always True about DomainModel
fact {all d: DomainModel | (R1 in d.relationship) and (R3 in  d.relationship) and 
(R7  in d.relationship) and (R8  in d.relationship) and (R9  in d.relationship)and
 (R13  in d.relationship) and ( R14  in d.relationship)
}

// Metamodel well-formedness constraints
fact {
	all d: DomainModel | all r: Relationship | r in d.relationship => 
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
Timers in p.config.feature => R5 in p.dm.relationship}

fact {all p: Product |
EmergencyAlarm in p.config.feature => R18 in p.dm.relationship}

fact {all p: Product |
FloorButtons in p.config.feature => R12 in p.dm.relationship}

fact {all p: Product |
ElevatorButtons in p.config.feature => R17 in p.dm.relationship}

fact {all p: Product | 
Sensors in p.config.feature => R4 in p.dm.relationship}

fact {all p: Product | 
MultipleElevators in p.config.feature =>
 ((R15 in p.dm.relationship) and (R16 in p.dm.relationship))}

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
WeightSensorInterface in p.dm.class
else WeightSensorInterface not in p.dm.class }

fact {all dec: DesignChoices | all s: dec.spl | all p: s.product |
IlluminatingLamps in dec.cm.choice =>
((R2 in p.dm.relationship) and (R10 in p.dm.relationship)
and (R11 in p.dm.relationship))
else ((R2 not in p.dm.relationship) and (R10 not in p.dm.relationship)
and (R11 not in p.dm.relationship))
}


fact{all dec: DesignChoices | all s: dec.spl | all p: s.product |
 EmergencyHandling in dec.cm.choice=>
R18 in p.dm.relationship
else R18 not in p.dm.relationship}

//symmetry breaking constraints
fact {all f1, f2 : FeatureModel | f1.feature = f2.feature => f1= f2}
fact {all d1, d2 : DomainModel | d1.relationship = d2.relationship => d1=d2}
fact {all t1, t2 : Relationship | (t1.from = t2.from) and (t1.to = t2.to) =>
t1=t2}
fact {all p1, p2 : Product | (p1.config = p2.config) and (p1.dm=p2.dm)=>
p1 = p2}

fact{all c1, c2 : ChoiceModel | c1.choice = c2.choice =>
c1 = c2}
fact {all dc1, dc2 : DesignChoices | dc1.cm = dc2.cm =>
dc1=dc2}

pred model{}
run model for 20




// All o/p devices are controlled by elevator control
//For All For All

assert controlling { all pl: SPL | all p: pl.product | 
all r : p.dm.relationship | ((r.label = Controls) and (r.to.interface= OutputDeviceInterface)) => r.from = ElevatorControl
  }

// There is no class related to itself
assert self { all pl: SPL | all p: pl.product | 
all r : p.dm.relationship | (r.to != r.from)
  }

// there is no direct relation between input device and output device interface
assert direct { all pl: SPL | all p: pl.product | 
no r : p.dm.relationship | (r.to.interface= InputDeviceInterface and  
r.from.interface = OutputDeviceInterface)
  }

// Gives product as counterexample
assert sch {all pl: SPL | all p: pl.product |  
all c : p.dm.class | ElevatorScheduler in c
  }

//for all exist
assert schexist {all pl: SPL | some p: pl.product |  
ElevatorScheduler in p.dm.class
  }

assert R18exist {all pl: SPL | some p: pl.product |  
R18 in p.dm.relationship
  }

//exist for all
assert schexist1 {some pl: SPL | all p: pl.product |  
R15 in p.dm.relationship
  }



check controlling for 20
check self for 20
check direct for 20
check sch for 20
check schexist for 20
check R18exist for 20
check schexist1 for 20

