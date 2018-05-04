// general definitions
abstract sig Feature{}
one sig Wash, Heat , Delay, Dry extends Feature{}

// FEATURE MODEL DEFINITION
abstract sig FeatureModel{
	feature: some Feature
}

// Wash is a necessary feature in all products
fact {
	all f: FeatureModel | Wash in f.feature
}

abstract sig State{}
one sig Locking, Waiting, Washing, Drying, Unlocking extends State{}

abstract sig Label{}
abstract sig Guard{}

abstract sig Transition{
	source: one State,
	target: one State,
	guard: lone Guard,
	label: lone Label
}
one sig Nospin extends Guard{}
one sig HeatEnabled_or_DelayEnabled , IncHeat, washstart, nospin, quickcool extends Label{}
one sig T1, T2, T3, T4, T5, T6 extends Transition{}

fact {(T1.source = Locking) and (T1.target = Waiting) and (T1.label = HeatEnabled_or_DelayEnabled) and (T1.guard= none)}
fact {(T2.source = Waiting) and (T2.target = Washing) and (T2.label = washstart) and (T2.guard= none)}
fact {(T3.source = Locking) and (T3.target = Washing) and (T3.label = washstart)and (T3.guard= none) }
fact {(T4.source = Washing) and (T4.target = Unlocking) and (T4.label = quickcool) and (T4.guard= none)}
fact {(T5.source = Washing) and (T5.target = Drying)}
fact {(T6.source = Drying) and (T6.target = Unlocking) and (T6.label = quickcool) and (T6.guard= none)}
//fact {(T7.source = Waiting) and (T7.target = Waiting) and (T7.label= IncHeat)and (T7.guard= none)}


// DOMAIN MODEL DEFINITION
// container for model elements, i.e., the domain model
sig DomainModel{
	transition: some Transition,
	state: some State
}
// Metamodel well-formedness constraints
fact {
	all d: DomainModel | all t: d.transition | t in d.transition => 
	(t.source in d.state) and (t.target in d.state)
}

//============================================================================================================
// Things we know for sure about all products
fact {all d: DomainModel | (T3 in d.transition) and (T4 in d.transition)  }


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


fact {
	all p: Product | 
			(Dry in p.config.feature)=>
			((T5 in p.dm.transition) and (T6 in p.dm.transition))
		else ((T5 not in p.dm.transition) and (T6 not  in p.dm.transition))
}

fact {
	all p: Product| 
		(Heat in p.config.feature) or (Delay in p.config.feature) =>
			((T1 in p.dm.transition) and (T2 in p.dm.transition))
		else ((T1 not in p.dm.transition) and (T2 not  in p.dm.transition))

}


//symmetry breaking constraints
fact {all f1, f2 : FeatureModel | f1.feature = f2.feature => f1= f2}
fact {all d1, d2 : DomainModel | d1.transition = d2.transition => d1=d2}
fact {all t1, t2 : Transition | (t1.source = t2.source) and (t1.target = t2.target) =>
t1=t2}
fact {all p1, p2 : Product | (p1.config = p2.config) and (p1.dm=p2.dm)=>
p1 = p2}


// to check there is always an initial state
assert initialState {all p: Product| some s: p.dm.state | 
(s in p.dm.transition.source) and (s not in  p.dm.transition.target)}

//to check there is always a final state
assert finalState {all p: Product| some s: p.dm.state | 
(s not in p.dm.transition.source) and (s in  p.dm.transition.target)}

//For All
// to check there exist some transitions having guards
assert transitionGuards{all p : Product | some t: p.dm.transition | t.guard !=none}

//exists
// to check there exist some transitions having guards
assert transitionGuardsexist{one p : Product | some t: p.dm.transition | t.guard !=none}


check initialState for 20
check finalState for 10
check transitionGuards for 10
check transitionGuardsexist for 10
