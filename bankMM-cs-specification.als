module Bank

//Names of fields/associations in classes of the model
abstract sig FName {}

//Parent of all classes relating fields and values
abstract sig Obj {}

//Types of fields
abstract sig Val {}


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


	//Features
	#cd.features = 5
	buildFeature[cd, Client, name, string]
	buildFeature[cd, Employee, name, string]
	buildFeature[cd, SavingsAccount, interestRate, double]
	buildFeature[cd, CheckingAccount, interestRate, double]
	buildFeature[cd, RetirementAccount, interestRate, double]

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




//check if there is a dead class in the class diagram
pred deadClass[cd: CD] {
	some c: cd.classes | isDeadClass[cd, c] 
}

//check if a class is a 'dead class'
pred isDeadClass[cd: CD, o:Obj] {
    //check if the class o does not have associations
	all x,y : associationEnd | (x->y in cd.associations) implies (not (o in x.class) and (not (o in y.class)))
    //check if the class o does not have inheritance relations
	all p:cd.classes | not o->p in cd.extensions and not p->o in cd.extensions
}


pred Exp2(cd: CD){
	initialConditions[cd]
	deadClass[cd]
} 

run  Exp2 for 17 but 1 CD



























