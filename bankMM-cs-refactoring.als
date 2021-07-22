open util/ordering[MetaState]


module Bank

//Names of fields/associations in classes of the model
abstract sig FName {}

//Parent of all classes relating fields and values
abstract sig Obj {}

//Types of fields
abstract sig Val {}

// Enums
sig Enum {
	values: set Obj
}


// Names of fields/associations in cd
one sig name extends FName {}
one sig interestRate extends FName {}

one sig branches extends FName {}
one sig atms extends FName {}
one sig bank extends FName {}
one sig clients extends FName {}
one sig client extends FName {}
one sig account extends FName {}
one sig transactions extends FName {}
one sig employees extends FName {}
one sig loan extends FName {}



// Types in model cd
one sig string extends Val {}
one sig double extends Val {}


// Classes in model cd
one sig Branch extends Obj {}
one sig ATM extends Obj {}
one sig Client extends Obj {}
one sig Transaction extends Obj {}
one sig Bank extends Obj {}
one sig Account extends Obj {}
one sig SavingsAccount extends Obj {}
one sig CheckingAccount extends Obj {}
one sig RetirementAccount extends Obj {}
one sig Employee extends Obj {}
one sig FullTimeEmployee extends Obj {}
one sig PartTimeEmployee extends Obj {}
one sig Loan extends Obj {}
one sig Affiliate extends Obj {}

one sig Entity extends Obj {}



//============================================================================================
// *****************************************************************Modifications****************************************************************
//============================================================================================

//Metamodel information
sig CD{
	classes: set Obj,
	enums: set Enum,
	associations: set associationEnd -> associationEnd,
	asso: set classes -> FName -> classes, // for visualization purposes
	extensions: classes -> classes,
	features: Obj -> FName -> Val
}

sig associationEnd{
	class: Obj,
	type: String,
	label: FName,
	lowerBound: Int ,
	upperBound: Int ,
}

pred buildAsso[cd:CD, obj1:Obj, label1:FName, _type:String, obj2:Obj, label2:FName, l1:Int, u1:Int, l2:Int, u2:Int]{
	one ae1,ae2:associationEnd | {

		ae1!=ae2

		ae1.class = obj1
		ae1.type=_type
		ae1.label=label1
		ae1.lowerBound=l1
		ae1.upperBound=u1

		ae2.class = obj2
		ae2.type=_type
		ae2.label=label2
		ae2.lowerBound=l2
		ae2.upperBound=u2

		ae1->ae2 in cd.associations

	}

	obj1 -> label1 -> obj2 in cd.asso
}


// o2 extends o1 in cd
pred buildExtension[cd:CD, o1:Obj, o2:Obj]{
	o2 -> o1 in cd.extensions
}


pred buildFeature[cd:CD, c: Obj, fn: FName, v: Val]{
	c->fn->v in cd.features
}



pred initialConditions[cd:CD]{


	//Classes
	//#cd.classes = 10
	cd.classes = {Branch+ATM+Client+Transaction+Bank+Account+SavingsAccount+
				CheckingAccount+RetirementAccount+Employee+FullTimeEmployee+
				PartTimeEmployee+Loan+Affiliate}

	//Associations
	//#cd.associations = 8
//	#cd.asso = 8
	buildAsso[cd,Bank,bank,"composition",Branch,branches,1,1,0,-1]
	buildAsso[cd,Bank,bank,"composition",ATM,atms,1,1,0,-1]
	buildAsso[cd,Bank,branches,"composition",Client,clients,1,1,0,-1]
	buildAsso[cd,Client,client,"unidirectional",Bank,bank,1,1,1,1]
	buildAsso[cd,Client,client,"bidirectional",Account,account,1,1,1,1]
	buildAsso[cd,Account,account,"composition",Transaction,transactions,1,1,0,-1]
	buildAsso[cd,Bank,bank,"composition",Employee,employees,1,1,1,-1]
	buildAsso[cd,Account,account,"bidirectional",Loan,loan,1,1,0,1]

	
	
	//Extensions
	#cd.extensions=5
	cd.extensions = {SavingsAccount->Account + CheckingAccount->Account + RetirementAccount->Account + 
				FullTimeEmployee->Employee + PartTimeEmployee->Employee}
	

	// no class that extends itself
	all c: cd.classes |not (c->c in cd.extensions)

	//Enums
	#cd.enums= 0

	//Features
	#cd.features = 5
	buildFeature[cd, Client, name, string]
	buildFeature[cd, Employee, name, string]
	//buildFeature[cd, SavingsAccount, interestRate, double]
	//buildFeature[cd, CheckingAccount, interestRate, double]
	//buildFeature[cd, RetirementAccount, interestRate, double]
	buildFeature[cd, Account, interestRate, double]

	//each class should belong to a CD
	all o:Obj-Entity | some cd:CD |o in cd.classes
	//each association is used once and should belong to a CD
	all ae1:associationEnd |some cdg:CD | one ae2:associationEnd |ae1->ae2 in cdg.associations or ae2->ae1 in cdg.associations

	all ae1:associationEnd |some cdg:CD | ae1.class in cdg.classes

	// all endAssociations map to objects associations and reciprocally: complete representation
	all ae1,ae2: associationEnd |some cdg:CD | (ae1->ae2 in cdg.associations) implies (ae1.class in cdg.classes)

	


}


pred Exp1(cd: CD){
	initialConditions[cd]
} 

run  Exp1 for 17 but 1 CD





pred Exp2(cd: CD){
	initialConditions[cd]
	deadClass[cd]
} 

run  Exp2 for 17 but 1 CD




//============================================================================================
//**************************************************************SMELLS DETECTION*********************************************************
//============================================================================================

//duplicated attr with common parent
pred isDuplicatedFeature[cd: CD, fn: FName, v: Val, parent: Obj] {
	#{child:cd.classes | child -> parent in cd.extensions}>1
	all child:cd.classes | child -> parent in cd.extensions implies child->fn->v in cd.features
}

//duplicated attr
pred isDuplicatedFeature2[cd: CD, fn: FName, v: Val] {
	#{c:cd.classes | c->fn->v in cd.features}>1
	//some c:cd.classes | c->fn->v in cd.features
}

//dead class smell
pred deadClass[cd: CD] {
	some c: cd.classes | isDeadClass[cd, c] 
	
}


pred isDeadClass[cd: CD, o:Obj] {
	all x,y : associationEnd | (x->y in cd.associations) implies (not (o in x.class) and not (o in y.class))

	all p:cd.classes | not o->p in cd.extensions and not p->o in cd.extensions
}




pred Exp2_find_DC(cd: CD){
	initialConditions[cd]
	deadClass[cd]
} run Exp2_find_DC for 9 but 1 CD, 1 State



pred Exp3_find_DF1(cd: CD){
	initialConditions[cd]
	some fn: FName, v: Val, p: Obj | isDuplicatedFeature[cd, fn, v, p]
} run Exp3_find_DF1 for 9 but 1 CD, 1 State


pred Exp4_find_DF2(cd: CD){
	initialConditions[cd]
	some fn: FName, v: Val | isDuplicatedFeature2[cd, fn, v] and no p: Obj | isDuplicatedFeature[cd, fn, v, p]
	
} run Exp4_find_DF2 for 9 but 1 CD, 1 State





//============================================================================================
//***************************************************************REFACTORING OPS**********************************************************
//============================================================================================





pred true {no none}
pred false {some none}






//remove dead class
pred refactor1[cd, cd': CD]{
	one x: cd.classes | {
			isDeadClass[cd,x]
			cd'.classes = cd.classes - x
			cd'.associations = cd.associations
			cd'.asso = cd.asso
			cd'.extensions = cd.extensions
			//cd'.features = cd.features // consider deleting features of dead class
			all fn: FName, v: Val, c: Obj | c=x implies not c->fn->v in cd'.features
										else c->fn->v in cd.features implies c->fn->v in cd'.features
										else not c->fn->v in cd'.features
	
		}
}

//pull-up field
pred refactor2[cd, cd': CD]{
	one fn: FName, v: Val | one op: cd.classes | {
	
			
			isDuplicatedFeature[cd, fn, v, op]
	
			all f: FName, vv: Val, c: Obj | 		c not in cd.classes implies not c->f->vv in cd'.features
											else (fn=f and vv=v and c->op in cd.extensions) implies { not c->f->vv in cd'.features}
											else c->f->vv in cd.features implies c->f->vv in cd'.features
											else (op=c and fn=f and vv=v) implies c->f->vv in cd'.features
											else not c->f->vv in cd'.features
											
			//cd'.features = cd'.features+op->fn->v
			cd'.classes = cd.classes
			cd'.	associations = cd.associations
			cd'.asso = cd.asso
			cd'.extensions = cd.extensions
		    
		}
}

//extract super class
pred refactor3[cd, cd': CD]{
	some fn: FName, v: Val | {
	
			
			isDuplicatedFeature2[cd, fn, v]
	

			all f: FName, vv: Val, c: Obj | (Entity = c and f=fn and v=vv ) implies c->f->vv in cd'.features
										else 
											c not in cd.classes implies not c->f->vv in cd'.features
										else
											(fn=f and vv=v and c->fn->v in cd.features) implies {
													//cd'.extensions=cd'.extensions+c->Element
													not c->fn->v in cd'.features
												}
											else 
												c->f->vv in cd.features implies c->f->vv in cd'.features
											else
												not c->f->vv in cd'.features
	
			cd'.classes = cd.classes + Entity
			# (cd'.classes & Entity) = 1
			cd'.	associations = cd.associations
			cd'.asso = cd.asso
			all c1,c2: Obj - Entity | c1->c2 in cd.extensions implies c1->c2 in cd'.extensions
									else not c1->c2 in cd'.extensions
			all c: Obj | not Entity->c in cd'.extensions and (
					(c->fn->v in cd.features and c in cd.classes) implies (c->Entity in cd'.extensions)
								else 
									not (c->Entity in cd'.extensions))

	
		}
}


//remove duplicated unidirectional assocition with composition
pred refactor4[cd, cd': CD]{
	one x, y: cd.classes | one a1, a2, a3, a4: associationEnd | {
			a1->a2 in cd.associations and a3->a4 in cd.associations
			a1.class = x and a2.class = y and a1.type = "composition"
			a3.class = y and a4.class = x and a3.type = "unidirectional"
			cd'.classes = cd.classes
			cd'.associations = cd.associations - a3->a4
			cd'.asso = cd.asso
			cd'.extensions = cd.extensions
			cd'.features = cd.features
	
		}
}



//classification by hierarchy to enumeration
pred refactor5[cd, cd': CD]{
	one x: cd.classes | all y: cd.classes | one e: Enum{
			
			y->x in cd.extensions implies no  f: FName, v: Val | y->f->v in cd.features
			cd'.classes = cd.classes - y
			cd'.associations = cd.associations
			cd'.asso = cd.asso
			cd'.extensions = cd.extensions - y->x
			cd'.features = cd.features
			y in e.values
			cd'.enums = cd.enums + e

		}
}


//============================================================================================
//***************************************************************Problem Formulation**********************************************************
//============================================================================================

//abstract sig OrderedState {}


sig MetaState {}

sig State extends MetaState{ 
	cd: one CD
}





//At most one item to move from 'from' to 'to'
pred refactorOperation[cd, cd': CD] {

	refactor1[cd, cd']
	or 
	refactor2[cd, cd']
	or
	refactor3[cd, cd'] 

}


fact {
  all s: State, s': s.next {
      s' in State implies refactorOperation [s.cd, s'.cd]
  }

	all c: CD | one s: State | s.cd = c
	all s: State | one c: CD  | s.cd = c
	
	first in State
	all ms: MetaState | no s: State | ms not in State and s in ms.next
//	#{s:State, s': s.next | s' in MetaState} <= 1
	
}




pred smellConstraint[threshold: Int]{
	#State >= int threshold + 1
}




pred Exp5_Ref {
	initialConditions[first.cd]
	smellConstraint[3]

	
} run Exp5_Ref for 7


pred Exp6_Ref {
	initialConditions[first.cd]
	smellConstraint[2]

	
} run Exp6_Ref for 6



//============================================================================================
//*********************************************************************** Quality ******************************************************************
//============================================================================================


// Design metrics
pred designSize[cd, cd': CD]{
	#cd'.classes<=#cd.classes
}



pred DIT[cd, cd': CD]{
	SDIT[cd]>=SDIT[cd']
}


fun MDIT[cd: CD]: one Int{
  	{
		ans:Int | (#cd.classes=0 implies ans = 0 else ans=div[SDIT[cd],#cd.classes] )
	}
}



fun SDIT[cd: CD]: one Int{
  	{
		ans:Int | ans = (sum e:cd.classes  | DIT1[cd, e])
	}
}


fun DIT1[cd: CD, c: Obj]: one Int {
	{ans:Int | ans =(#c.*(cd.extensions)) }
}


fun NC[cd: CD]: one Int {
    {ans:Int | ans = #cd.classes}
}


fun NR[cd: CD]: one Int {
    {ans:Int | ans = #cd.associations}
}


fun NCR[cd: CD]: one Int {
    {ans:Int | ans = #{l,r: associationEnd | l->r in cd.associations and ( l.type="composition" or r.type="composition")}}
}

fun NUR[cd: CD]: one Int {
    {ans:Int | ans = #{l,r: associationEnd | l->r in cd.associations and ( l.type="unidirectional" or r.type="unidirectional")}}
}

fun NA[cd: CD]: one Int {
    {ans:Int | ans = #cd.features}
}


fun DITset[cd: CD]: set Int{
  	{
		ans: Int | all e:cd.classes  | DIT1[cd, e] in ans // problem
	}
}

fun DITmax[cd: CD]: one Int{
  	{
		ans:Int | ans = max [DITset[cd]]
	}
}


fun NGenH[cd: CD]: one Int{
  	{
		ans:Int | ans = #cd.extensions
	}
}


fun PRED[cd: CD]: one Int{
  	{
		ans:Int | ans = (sum e:cd.classes  | DIT1[cd, e])
	}
}



fun Ad[cd: CD]: one Int {
    {ans:Int | ans = #cd.features}
}


fun Ai[cd: CD, c: Obj]: one Int {
    {ans:Int | ans = (mul [ minus[ (#c.*(~(cd.extensions))), 1] , #c.(cd.features) ] ) }
}

fun Ai[cd: CD]: one Int {
    { ans:Int | ans = (sum e:cd.classes  | Ai[cd, e]) }
}



// Quality attributes


fun Maintainability[cd: CD]: one Int{
  	{
		ans:Int | ans = negate[sum {NC[cd] + NA[cd] + NR[cd] + DITmax[cd] + NGenH[cd]}]
	}
}


fun Understandability[cd: CD]: one Int{
  	{
	//	ans:Int | ans = div[PRED[cd] + 1 , NC[cd] ]
		ans:Int | ans = PRED[cd] + 1
	}
}

 
fun Extendibility[cd: CD]: one Int{
  	{
		ans:Int | ans = div [ Ai[cd] , Ad[cd] ]
	}
}

fun Complexity[cd: CD]: one Int{
  	{
		ans:Int | ans = negate[sum{ minus[NR[cd], NUR[cd]] + Understandability[cd] + minus[NR[cd], NCR[cd]] }]
	}
}


//quality assurance
pred QA[cd, cd': CD, q: set String]{
	"Maintainability" in q implies lte[Maintainability[cd], Maintainability [cd']]
	"Understandability" in q implies lte[Understandability[cd], Understandability [cd']]
	"Extendibility" in q implies lte[Extendibility[cd], Extendibility [cd']]
	"Complexity" in q implies lte[Complexity[cd], Complexity [cd']]
}


fun get_last[]: one State {
    { s:State | s.next not in State}
}


pred Exp7_QRef {
	initialConditions[first.cd]
	smellConstraint[2]
	QA[first.cd, get_last.cd, {"Maintainability" + "Understandability" + "Extendibility" + "Complexity"}]
	
} run Exp7_QRef for 6


pred Exp8_QRef {
	initialConditions[first.cd]
	smellConstraint[3]
	QA[first.cd, get_last.cd, {"Maintainability" + "Understandability" + "Extendibility" + "Complexity"}]
	
} run Exp8_QRef for 6 but 7 Int


pred Exp9_QRef {
	initialConditions[first.cd]
	smellConstraint[2]
	QA[first.cd, get_last.cd, {"Complexity" + "Maintainability"}]
	
} run Exp9_QRef for 6 but 7 Int


pred Exp10_QRef {
	initialConditions[first.cd]
	smellConstraint[2]
	QA[first.cd, get_last.cd, {"Extendibility" + "Understandability"}]
	
} run Exp10_QRef for 12 but 7 Int, 3 State































