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
one sig InsertCard, InsertPin, InsertAmount, TakeCash, DepositCash,
 Print_Receipt extends State{}

abstract sig Transition{
	source: one State,
	target: one State,
	guard: lone Guard
	//label: lone Label
}

sig ClassDiagram{}


sig StateChart{
	transition: some Transition,
	state: some State
}


abstract sig DomainModel{
cd: lone ClassDiagram,
sc: lone StateChart
}




// Metamodel well-formedness constraints
fact {
	all d: DomainModel | all t: d.sc.transition | t in d.sc.transition => 
	(t.source in d.sc.state) and (t.target in d.sc.state)
}


one sig T1, T2, T3, T4, T5, T6 extends Transition{}
fact {(T1.source = InsertCard) and (T1.target = InsertPin)and (T1.guard= none)}
fact {(T2.source = InsertPin) and (T2.target = InsertAmount) and (T2.guard = none)}
fact {(T3.source = InsertAmount) and (T3.target = TakeCash) and (T3.guard= none)}
fact {(T4.source = InsertAmount) and (T4.target = DepositCash) and (T4.guard = none)}
fact {(T5.source = TakeCash) and (T5.target = Print_Receipt) and (T5.guard = PaperRoll)}
fact {(T6.source = DepositCash) and (T6.target = Print_Receipt) and (T6.guard= PaperRoll)}

// Things we know for sure about all products
fact {all d: DomainModel | (T1 in d.sc.transition) and (T2 in d.sc.transition)  }

//Product Definition
abstract sig Product{
dm: one DomainModel,
config: one FeatureModel}

//Well formdness rules
fact{all f: FeatureModel | f in Product.config}
fact{all d: DomainModel | d in Product.dm}

//Product line definition
abstract sig SPL{
product : some Product
}

fact {all p: Product | p in SPL.product}

//Feature Mapping
fact {all p: Product | Withdraw in p.config.feature =>
((T3 in p.dm.sc.transition) )
else( (T3 not in p.dm.sc.transition) )}


fact {all p: Product | Deposit in p.config.feature =>
((T4 in p.dm.sc.transition) )
else( (T4 not in p.dm.sc.transition))}

fact {all f1, f2 : FeatureModel | f1.feature = f2.feature => f1= f2}
fact {all d1, d2 : StateChart | d1.transition = d2.transition => d1=d2}
fact {all t1, t2 : Transition | (t1.source = t2.source) and (t1.target = t2.target) =>
t1=t2}
fact{all d1, d2: DomainModel | d1.sc=d2.sc=> d1=d2}
fact {all p1, p2 : Product | (p1.config = p2.config) and (p1.dm=p2.dm)=>
p1 = p2}
one sig P1, P2, P3, P4, P5, P6  extends Product{}



//SPLDCs
//Choices
abstract sig Choice{}
one sig Multitask, Receipt extends Choice{}

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

//decision Mapping
fact DecMapMulti{ all dec: DesignChoices | all s: dec.spl | all p: s.product | 
Multitask in dec.cm.choice => 
((Withdraw in p.config.feature) and (Deposit in p.config.feature))}

fact { all dec: DesignChoices | all s: dec.spl | all p: s.product | 
((Receipt in dec.cm.choice) and (Withdraw in p.config.feature) )=> 
(T5 in p.dm.sc.transition)
else (T5 not in p.dm.sc.transition)}


fact { all dec: DesignChoices | all s: dec.spl | all p: s.product | 
((Receipt in dec.cm.choice) and (Deposit in p.config.feature)) => 
(T6 in p.dm.sc.transition)
else (T6 not in p.dm.sc.transition)}

fact{all d:DomainModel | ((T5 in d.sc.transition) or (T6 in d.sc.transition)) =>
Print_Receipt in d.sc.state
else Print_Receipt not in d.sc.state}

//symmetry breaking constraints
fact{all c1, c2 : ChoiceModel | c1.choice = c2.choice =>
c1 = c2}
fact {all dc1, dc2 : DesignChoices | dc1.cm = dc2.cm =>
dc1=dc2}


//for all spl and for all products
assert initialState {all pl: SPL | all p: pl.product|  all dm: p.dm | one s: dm.sc.state | 
(s in dm.sc.transition.source) and (s not in  dm.sc.transition.target)}

assert finalState {all pl: SPL | all p: pl.product| all dm: p.dm |  some s: dm.sc.state | 
(s not in dm.sc.transition.source) and (s in  dm.sc.transition.target)}

//here it gives counteexample because there are some PL where it does not hold
assert transitionGuards{all pl: SPL|all p : pl.product |  all dm: p.dm | 
 some t: dm.sc.transition | t.guard !=none}

// gives counter example so we will check for another level
assert withdraw{all pl: SPL|all p : pl.product | all dm: p.dm |  T4 in dm.sc.transition}


//Exist SPL all products
// This does not give counterexample
assert transitionGuardsomepl{some pl: SPL|all p : pl.product |  all dm: p.dm | 
 some t: dm.sc.transition | t.guard !=none}

pred transitionGuardsomepl{some pl: SPL|all p : pl.product |  all dm: p.dm | 
 some t: dm.sc.transition | t.guard !=none}

//still gives counterexample, so we check for another level
assert withdrawSomepl{some pl: SPL|all p : pl.product |  all dm: p.dm | T4 in dm.sc.transition}


//all spl exist product
//here does not find counterexample, so this is its correct level
assert withdrawAllpl{all pl: SPL|some p : pl.product |  all dm: p.dm | T4 in dm.sc.transition}

pred withdrawAllpl{all pl: SPL|some p : pl.product | all dm: p.dm |  T4 in dm.sc.transition}


//exist exist
pred withdrawAllpl1{some pl: SPL|some p : pl.product |  all dm: p.dm | T4 in dm.sc.transition}

//no guards NA
assert NoGuardsNA{all pl: SPL|all p : pl.product |  all dm: p.dm | 
 all t: dm.sc.transition | t.guard =none}


//no guards NS
assert NoGuardsNS{all pl: SPL|some p : pl.product |  all dm: p.dm | 
 all t: dm.sc.transition | t.guard =none}

//no guards PA
assert NoGuardsPA{some pl: SPL|all p : pl.product | all dm: p.dm | 
 all t: dm.sc.transition | t.guard =none}

//oneFinalNA
assert oneFinalNA {all pl: SPL | all p: pl.product| all dm: p.dm | one s: dm.sc.state | 
(s not in dm.sc.transition.source) and (s in  dm.sc.transition.target)}

//oneFinalNS
assert oneFinalNS {all pl: SPL | some p: pl.product|  all dm: p.dm | one s: dm.sc.state | 
(s not in dm.sc.transition.source) and (s in  dm.sc.transition.target)}

//oneFinalPA
assert oneFinalPA {some pl: SPL | all p: pl.product|all dm: p.dm | one s: dm.sc.state | 
(s not in dm.sc.transition.source) and (s in  dm.sc.transition.target)}


check initialState for 10
check transitionGuards for 10
check transitionGuardsomepl for 10
check withdraw for 10
check withdrawSomepl for 10
check withdrawAllpl for 10
check finalState for 10
check NoGuardsNA for 10
check NoGuardsNS for 10
check NoGuardsPA for 10
check oneFinalNA for 10
check oneFinalNS for 10
check oneFinalPA for 10
