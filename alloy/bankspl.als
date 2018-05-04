// BASIC DEFINITIONS
abstract sig Feature{}
one sig Withdraw, Deposit extends Feature{}

// FEATURE MODEL DEFINITION
abstract sig FeatureModel{
	feature: some Feature
}

//DomainModel Definition
abstract sig Guard{}
one sig PaperRoll extends Guard{}

abstract sig State{}
one sig InsertCard, InsertPin, InsertAmount, TakeCash, DepositCash, Receipt extends State{}

abstract sig Transition{
	source: one State,
	target: one State,
	guard: lone Guard
	//label: lone Label
}

sig DomainModel{
	transition: some Transition,
	state: some State
}


// Metamodel well-formedness constraints
fact {
	all d: DomainModel | all t: d.transition | t in d.transition => 
	(t.source in d.state) and (t.target in d.state)
}


one sig T1, T2, T3, T4, T5, T6 extends Transition{}
fact {(T1.source = InsertCard) and (T1.target = InsertPin)and (T1.guard= none)}
fact {(T2.source = InsertPin) and (T2.target = InsertAmount) and (T2.guard = none)}
fact {(T3.source = InsertAmount) and (T3.target = TakeCash) and (T3.guard= none)}
fact {(T4.source = InsertAmount) and (T4.target = DepositCash) and (T4.guard = none)}
fact {(T5.source = TakeCash) and (T5.target = Receipt) and (T5.guard = PaperRoll)}
fact {(T6.source = DepositCash) and (T6.target = Receipt) and (T6.guard= PaperRoll)}

// Things we know for sure about all products
fact {all d: DomainModel | (T1 in d.transition) and (T2 in d.transition)  }

//Product Definition
abstract sig Product{
dm: one DomainModel,
config: one FeatureModel}

//Well formdness rules
fact{all f: FeatureModel | f in Product.config}
fact{all d: DomainModel | d in Product.dm}

//Product line definition
one sig SPL{
product : some Product
}

fact {all p: Product | p in SPL.product}
fact {all p: Product | Withdraw in p.config.feature =>
((T3 in p.dm.transition) and (T5 in p.dm.transition))
else( (T3 not in p.dm.transition) and (T5 not in p.dm.transition))}


fact {all p: Product | Deposit in p.config.feature =>
((T4 in p.dm.transition) and (T6 in p.dm.transition))
else( (T4 not in p.dm.transition) and (T6 not in p.dm.transition))}

fact {all f1, f2 : FeatureModel | f1.feature = f2.feature => f1= f2}
fact {all d1, d2 : DomainModel | d1.transition = d2.transition => d1=d2}
fact {all t1, t2 : Transition | (t1.source = t2.source) and (t1.target = t2.target) =>
t1=t2}
fact {all p1, p2 : Product | (p1.config = p2.config) and (p1.dm=p2.dm)=>
p1 = p2}
one sig P1, P2, P3 extends Product{}
//fun init [s: State]: State {s not in DomainModel.transition.target}

//For All
// to check there exist some transitions having guards
assert transitionGuards{all p : Product | some t: p.dm.transition | t.guard !=none}

//to check only one transition has guard
// Here it gives the counterexample which shows the product that violates the property 
//along with its configuration
assert transitionGuardone{all p : Product | one t: p.dm.transition | t.guard !=none}

// to check there is always an initial state
assert initialState {all p: Product| one s: p.dm.state | 
(s in p.dm.transition.source) and (s not in  p.dm.transition.target)}

//to check there is always a final state
assert finalState {all p: Product| one s: p.dm.state | 
(s not in p.dm.transition.source) and (s in  p.dm.transition.target)}

//Exists
//So the assertion transitionGuardone does not hold for all products,
// but it holds for some products.
assert transitionGuardexist{some p : Product | one t: p.dm.transition | t.guard !=none}


pred model{}
run model for 10
check initialState for 10
check finalState for 10
check transitionGuards for 10
check transitionGuardexist for 10
