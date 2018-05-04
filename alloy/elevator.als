// BASIC DEFINITIONS
abstract sig Feature{}
one sig Lights, Weight, TwoThirdsFull, FCFS, SSTF extends Feature{}

abstract sig Decision{}
one sig EmergencyAlarm, DoorSignals, FCFSalgo, ElevatorLights  extends Decision{}


// FEATURE MODEL DEFINITION
abstract sig FeatureModel{
	feature: some Feature
}


//============================================================================================================
// MODELLING DECISIONS THAT IMPACT FEATURES
// container for the mapping between Decision and Feature Model
sig FeatureDecision{
decision: some Decision,
featureModel: one FeatureModel
}



//============================================================================================================
// MODELLING DECISIONS THAT IMPACT THE DOMAIN MODEL
// container of the mapping between Decisions and the Domain Model
sig DomainDecision{
	decision: some Decision,
	domainModel: one DomainModel
}

// SET OF ALL DECISIONS
// a container for both decisions that impact features and decisions that impact
// the domain model
sig DecisionModel{
	featureDecision: one FeatureDecision,
	domainDecision: one DomainDecision
}


sig DomainModel{
	relation: some Relation,
	class: some Class
}


abstract sig Class{
attribute : set Attribute,
method : set Method
}
one sig Elevator, El_Controller, Weight_Sensor, Request, Door, Button, El_Lights, Floor_Button,
El_Button, Alarm_Button extends Class{}


abstract sig Attribute{}
one sig direction, currentFloor, floorNo, maxWeight, warningMessage, algorithm,
doorOpen, buttonID, illuminate extends Attribute{}

abstract sig Method{}
one sig startEl, shutDown, reset, addRequest, ignoreRequest, openSignal, closeSignal extends Method{}

abstract sig RelationType{}
one sig Association, Aggregation extends RelationType{}

abstract sig Relation{
from: one Class,
to: one Class,
type: one RelationType
}

one sig R1, R2, R3, R4, R5, R6, R7, R8, R9 extends Relation{}

fact{R1.from = Elevator and R1.to=El_Controller and R1.type = Association}
fact{R2.from = El_Controller and R2.to=Weight_Sensor and R2.type = Association}
fact{R3.from = El_Controller and R3.to=Request and R3.type = Association}
fact{R4.from = El_Controller and R4.to=Door and R4.type = Association}
fact{R5.from = El_Controller and R5.to=El_Lights and R5.type = Association}
fact{R6.from = El_Controller and R6.to=Button and R6.type = Association}
fact{R7.from = Button and R7.to= Floor_Button and R7.type = Aggregation}
fact{R8.from = Button and R8.to= El_Button and R8.type = Aggregation}
fact{R9.from = Button and R9.to= Alarm_Button and R9.type = Aggregation}



fact {
	all r : Relation | r in DomainModel.relation <=> 
	(r.from in DomainModel.class) and (r.to in DomainModel.class)
}


//============================================================================================================
//facts about domain model

fact {all d: DomainModel | (R1 in d.relation) and (R3 in d.relation)
and (R4 in d.relation) and (R6 in d.relation)  and (R7 in d.relation) and (R8 in d.relation)  
}

fact { (direction in Elevator.attribute) and (currentFloor in Elevator.attribute)}
fact {(floorNo in El_Controller.attribute) and ((startEl in El_Controller.method)) and
(shutDown in El_Controller.method) and (reset in El_Controller.method)}

fact {(algorithm in Request.attribute) and (addRequest in Request.method) and 
(ignoreRequest in Request.method)}

fact {(doorOpen in Door.attribute)}

fact {(buttonID in Button.attribute) and (illuminate in Button.attribute)}
fact {(illuminate in El_Lights.attribute)}

//inheriting attributes and methods
fact {all r: Relation | r.type = Aggregation =>
(r.from.attribute in r.to.attribute ) and (r.from.method in r.to.method)}
//============================================================================================================
// FEATURE MAPPING aka Correspondance
sig Correspondance{
	featureModel: one FeatureModel,
	domainModel: one DomainModel
}

// Constraints to derive DomainModel from FeatureModel
// Constraints from the feature model that impact the domain model

fact {all c : Correspondance | Lights in c.featureModel.feature =>
R5 in c.domainModel.relation}

fact {all c : Correspondance | Weight in c.featureModel.feature =>
R2 in c.domainModel.relation}



//============================================================================================================
// DECISION MAPPING 
// Constraints to derive DomainModel from Domain decisions
fact {
	all d: DomainDecision | 
		(EmergencyAlarm in d.decision) =>
			R9 in d.domainModel.relation
		else R9 not in d.domainModel.relation
}


fact {
	all d: DomainDecision | 
		(DoorSignals in d.decision) =>
			((openSignal in Door.method) and (closeSignal in Door.method))
		else ((openSignal not in Door.method) and (openSignal not in Door.method))
}

fact {
	all f: FeatureDecision | 
		(ElevatorLights in f.decision) =>
			(Lights in f.featureModel.feature)
		else (Lights not in f.featureModel.feature)
}



//============================================================================================================
//SYMMETRY BREAKING CONSTRAINTS
// for the domain model
fact {all d1, d2 : DomainModel | (d1.relation = d2.relation) and (d1.class=d2.class) => d1=d2}
fact {all r1, r2 : Relation | (r1.from = r2.from) and (r1.to = r2.to) =>
r1=r2}

// for the spldc
fact {all f1, f2 : FeatureModel | f1.feature = f2.feature => f1= f2}
fact {all d1, d2 : DomainDecision | (d1.domainModel = d2.domainModel) => d1 = d2 }
fact {all f1, f2 : FeatureDecision | f1.featureModel = f2.featureModel => f1 = f2}
//============================================================================================================



//for all decM and for all fm
// A DOMAIN MODEL NEEDS TO FOLLOW FROM BOTH A FEATURE MAPPING AND A DECISION MAPPING
fact {all d: DomainModel    | d in DomainDecision.domainModel}
fact {all c: Correspondance | all d: DomainDecision | c.domainModel in d.domainModel}
fact {all c: Correspondance | all d: DomainDecision | d.domainModel in c.domainModel}
assert b {all d: DomainModel | R1 in d.relation}
//assert c {all d: DomainModel | T3 in d.transition}
//assert d {all d: DomainModel | Deposit in d.state}


//for all decM
//fact {all d: DomainModel    | d in DomainDecision.domainModel}
//assert b {all d: DomainModel | T1 in d.transition}
//assert c {all d: DomainModel | T3 in d.transition}
//assert d {all d: DomainModel | Deposit in d.state}

//for all FeatureModel
//fact {all d: DomainModel    | d in Correspondance.domainModel}
//assert b {all d: DomainModel | T1 in d.transition}
//assert c {all d: DomainModel | T3 in d.transition}
//assert d {all d: DomainModel | Deposit in d.state}


//There exist any
//fact {all d: DomainModel    | d in DomainDecision.domainModel}
//fact {all c: Correspondance | all d: DomainDecision | c.domainModel in d.domainModel}
//fact {all c: Correspondance | all d: DomainDecision | d.domainModel in c.domainModel}
//pred a { all d: DomainModel | T3 in d.transition}
//pred b {all d: DomainModel | T1 in d.transition}
//pred c {all d: DomainModel | Deposit in d.state}



check b for 20
