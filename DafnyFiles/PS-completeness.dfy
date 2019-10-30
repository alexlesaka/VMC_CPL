include "Proof-System.dfy"

module PS_Completeness {
	import opened Utils
	import opened QCSP = QCSP_Instance`Lemmas_for_PS_Completeness
	import opened PS = Proof_System`Lemma_and_Defs 
	export function_methods_for_Implementation 
	       reveals  projection, canonical_judgement, join, dualProjection
		   provides Utils, QCSP, PS

// Operations on Judgements 
function method projection<T>(j:Judgement<T>, U:set<Name>, phi:Formula, B:Structure<T>):Judgement<T>
	requires wfJudgement(j,phi,B) 
	requires U <= j.V
	ensures wfJudgement(projection(j,U,phi,B),phi,B)
	ensures is_projection(projection(j,U,phi,B),j,phi,B)
{
J(j.i, U, (set f | f in j.F  :: projectVal(f,U)))									
}
		
function join<T>(j1:Judgement<T>, j2:Judgement<T>, phi:Formula, B:Structure<T>):Judgement<T>
	requires wfJudgement(j1,phi,B) && wfJudgement(j2,phi,B)
	requires j1.i == j2.i
	ensures wfJudgement(join(j1,j2,phi,B),phi,B)  
	ensures is_join(join(j1,j2,phi,B),j1,j2,phi,B)
{
J(j1.i, j1.V+j2.V, (set f:Valuation<T> | f in allMaps(j1.V+j2.V, B.Dom) 
                                         && projectVal(f,j1.V) in j1.F 
										 && projectVal(f,j2.V) in j2.F))
}

function dualProjection<T>(v:Name, j:Judgement<T>, phi:Formula, B:Structure<T>): Judgement<T>
	requires wfJudgement(j,phi,B)
	requires |j.i| > 0 && j.i[..|j.i|-1] + [0] ==j.i 
	requires j.i[..|j.i|-1] in setOfIndex(phi)
	requires FoI(j.i[..|j.i|-1], phi, B.Sig).Forall? && FoI(j.i[..|j.i|-1], phi, B.Sig).x == v
	requires v in j.V 
	ensures wfJudgement(dualProjection(v, j, phi, B), phi, B)
	ensures is_dualProjection(dualProjection(v, j, phi,B),v,j,phi,B)
{
indexSubformula_Lemma(j.i[..|j.i|-1],phi, B.Sig);
J(j.i[..|j.i|-1], j.V-{v}, (set f:Valuation<T> | f in allMaps(j.V-{v},B.Dom) 
                                                 && forall b :: b in B.Dom ==> f[v:=b] in j.F))
}

function canonical_judgement<T> (i:seq<int>,phi:Formula,B:Structure<T>):Judgement<T>
	requires wfQCSP_Instance(phi,B)
	requires i in setOfIndex(phi)
	ensures canonical_judgement(i,phi,B).i == i
	ensures canonical_judgement(i,phi,B).V == freeVar(FoI(i,phi,B.Sig))
	ensures wfJudgement(canonical_judgement(i,phi,B),phi,B)  
	decreases FoI(i,phi,B.Sig)
{
var phii := FoI(i,phi,B.Sig); 
match phii
	case Atom(R,par) => var F := (set f:Valuation<T> | f in allMaps(setOf(par),B.Dom)	
								                        &&  HOmap(f,par) in B.I[R]);
						J(i, setOf(par), F)
	case And(phi0,phi1) =>	indexSubformula_Lemma(i,phi,B.Sig);
	                        var j0' := canonical_judgement(i+[0], phi, B);
							var j1' := canonical_judgement(i+[1], phi, B);
		 					var j0 := J(i, j0'.V, j0'.F);
							var j1 := J(i, j1'.V, j1'.F);
							join(j0, j1, phi, B)
	case Forall(x,phik) =>  indexSubformula_Lemma(i,phi,B.Sig);
	                        var j0 := canonical_judgement(i+[0],phi,B);								   
							if x in j0.V then dualProjection(x,j0,phi,B) else J(i,j0.V,j0.F)
	case Exists(x,phik) => indexSubformula_Lemma(i,phi,B.Sig);
	                       var j0:= canonical_judgement (i+[0],phi,B);
						   var jp := projection(j0,j0.V-{x},phi,B);
						   if x in j0.V then  J(i, jp.V, jp.F) else J(i,j0.V,j0.F)
}

//Sets of Valuations that are models of phi in an structure B
function setOfValmodels<T> (phi:Formula, B:Structure<T>):set<Valuation<T>>
	requires wfStructure(B) && wfFormula(B.Sig,phi)
{
(set f:Valuation<T> | f in allMaps(freeVar(phi), B.Dom) && models(B,f,phi))
}

lemma setofValmodelsAnd_Lemma<T>(phi0:Formula, phi1:Formula, B:Structure<T>)
    requires wfStructure(B) && wfFormula(B.Sig, phi0) && wfFormula(B.Sig, phi1)
   	ensures setOfValmodels(And(phi0,phi1),B) ==
            (set f:Valuation<T> |  f in allMaps(freeVar(phi0)+freeVar(phi1), B.Dom) 
	                               && projectVal(f,freeVar(phi0)) in setOfValmodels(phi0,B) 
							       && projectVal(f,freeVar(phi1)) in setOfValmodels(phi1,B));
{
var F := (set f:Valuation<T> |  f in allMaps(freeVar(phi0)+freeVar(phi1), B.Dom) 
	                          && projectVal(f,freeVar(phi0)) in setOfValmodels(phi0,B) 
							  && projectVal(f,freeVar(phi1)) in setOfValmodels(phi1,B));
forall f:Valuation<T> | f in F ensures f in setOfValmodels(And(phi0,phi1),B); 
    {
	assert projectVal(f,freeVar(phi0)) in allMaps(freeVar(phi0),B.Dom)  
		   && projectVal(f,freeVar(phi0)).Values <= B.Dom && models(B,projectVal(f,freeVar(phi0)),phi0)
		   && projectVal(f,freeVar(phi1)) in allMaps(freeVar(phi1),B.Dom) 
		   && projectVal(f,freeVar(phi1)).Values <= B.Dom && models(B,projectVal(f,freeVar(phi1)),phi1);
	modelsAnd_Lemma(B,f,And(phi0,phi1)); 
	assert f in allMaps(freeVar(And(phi0,phi1)), B.Dom) && f.Values <= B.Dom 
				&& models(B,f,And(phi0,phi1));
	assert f in setOfValmodels(And(phi0,phi1),B);
    }
//assert forall f:Valuation<T> :: f in F ==> f in setOfValmodels(And(phi0,phi1),B); 
forall f:Valuation<T> | f in setOfValmodels(And(phi0,phi1),B) ensures f in F
	{ 
	// assert f in allMaps(freeVar(And(phi0,phi1)), B.Dom) && wfModel(B,f,And(phi0,phi1)) 
	//            && models(B,f,And(phi0,phi1));
	modelsAnd_Lemma(B,f,And(phi0,phi1)); 
	assert projectVal(f,freeVar(phi0)).Values <= B.Dom && models(B,projectVal(f,freeVar(phi0)),phi0)
		   && projectVal(f,freeVar(phi1)).Values <= B.Dom && models(B,projectVal(f,freeVar(phi1)),phi1);
	allMaps_Correct_Lemma(projectVal(f,freeVar(phi0)),B.Dom);
	assert projectVal(f,freeVar(phi0)) in allMaps(freeVar(phi0),B.Dom);
	assert projectVal(f,freeVar(phi0)) in setOfValmodels(phi0,B);
	allMaps_Correct_Lemma(projectVal(f,freeVar(phi1)),B.Dom);
	assert projectVal(f,freeVar(phi1)) in allMaps(freeVar(phi1),B.Dom);
	assert projectVal(f,freeVar(phi1)) in setOfValmodels(phi1,B);
	assert f in F;
	}
//assert forall f:Valuation<T> :: f in setOfValmodels(And(phi0,phi1),B) ==> f in F;
}

lemma setofValmodelsForall_Lemma<T>(x:Name, beta:Formula,B:Structure<T>)
    requires wfStructure(B) && wfFormula(B.Sig, Forall(x,beta)) 
	requires x in freeVar(beta)
	ensures setOfValmodels(Forall(x,beta),B)
            == (set f:Valuation<T> | f in allMaps(freeVar(beta)-{x},B.Dom) 
                                     && forall b :: b in B.Dom ==> f[x:=b] in setOfValmodels(beta,B));
{	
var F := (set f:Valuation<T> | f in allMaps(freeVar(beta)-{x},B.Dom) 
                               && forall b :: b in B.Dom ==> f[x:=b] in setOfValmodels(beta,B));	
forall f:Valuation<T> | f in F
	ensures f in setOfValmodels(Forall(x,beta),B);
	{ 
	assert f in allMaps(freeVar(Forall(x,beta)), B.Dom);
	assert f.Values <= B.Dom;
	assert models(B,f,Forall(x,beta));
	}
//assert forall f:Valuation<T>:: f in F ==> f in setOfValmodels(Forall(x,beta),B);
forall f:Valuation<T>  | f in setOfValmodels(Forall(x,beta),B)
	ensures f in F;
	{ 
	assert f in allMaps(freeVar(beta)-{x}, B.Dom) && models(B,f,Forall(x,beta));
	forall b | b in B.Dom 
		ensures f[x:=b] in setOfValmodels(beta,B);
		{
		assert f[x:=b].Values <= B.Dom;
		assert models(B, f[x:=b], beta);
		ExtMap_Lemma(f, x, b, freeVar(beta), B.Dom);
		assert f[x:=b] in allMaps(freeVar(beta), B.Dom); 
		assert f[x:=b] in setOfValmodels(beta,B);
		}
	assert forall b :: b in B.Dom ==> f[x:=b] in setOfValmodels(beta,B);
	assert f in F;
	}
//assert forall f:Valuation<T>:: f in setOfValmodels(Forall(x,beta),B) ==> f in F;
}

lemma setofValmodelsExists_Lemma<T>(x:Name, beta:Formula,B:Structure<T>)
    requires wfStructure(B) && wfFormula(B.Sig, Exists(x,beta))
	requires x in freeVar(beta)
   	ensures setOfValmodels(Exists(x,beta),B) 
	        == (set h | h in setOfValmodels(beta,B) :: projectVal(h,freeVar(beta)-{x}))
{
var F := (set h | h in setOfValmodels(beta,B) :: projectVal(h,freeVar(beta)-{x}));
forall f:Valuation<T> | f in setOfValmodels(Exists(x,beta),B) 
	ensures f in F;
    {
	var v :| v in B.Dom && models(B,f[x:=v],beta);
	var h := f[x:=v];
	ExtMap_Lemma(f, x, v, freeVar(beta), B.Dom);
    assert h in allMaps(freeVar(beta), B.Dom);
	assert h in setOfValmodels(beta,B);
	assert f == projectVal(h,freeVar(beta)-{x});
	assert f in F;
	}
//assert forall f:Valuation<T> :: f in setOfValmodels(Exists(x,beta),B) ==> f in F;
forall f:Valuation<T> | f in F
	ensures f in setOfValmodels(Exists(x,beta),B);
    {
	var h :| h in setOfValmodels(beta,B) && f == projectVal(h,freeVar(beta)-{x});
	assert h in allMaps(freeVar(beta), B.Dom);
	ProyectMap_Lemma(h, freeVar(beta)-{x}, freeVar(beta), B.Dom);
	assert f in allMaps(freeVar(beta)-{x}, B.Dom);
	// assert models(B,h,beta);
	Existsmodels_Lemma(B, h, x, beta);
	// assert models(B,projectVal(h,freeVar(beta)-{x}),Exists(x,beta));
	assert models(B,f,Exists(x,beta));
	assert f in setOfValmodels(Exists(x,beta),B);
	}
//assert forall f:Valuation<T> ::  f in F ==> f in setOfValmodels(Exists(x,beta),B);
}

lemma canonical_judgement_Lemma<T>(i:seq<int>, phi:Formula, B:Structure<T>)
	requires wfQCSP_Instance(phi,B)
	requires i in setOfIndex(phi)
	ensures canonical_judgement(i,phi,B).i == i
	ensures canonical_judgement(i,phi,B).V == freeVar(FoI(i,phi,B.Sig))
	ensures canonical_judgement(i,phi,B).F == setOfValmodels(FoI(i,phi,B.Sig),B);
	ensures is_derivable(canonical_judgement(i,phi,B),phi,B)
	decreases FoI(i,phi,B.Sig)
{
var phii := FoI(i,phi,B.Sig);
if !phii.Atom? { indexSubformula_Lemma(i,phi,B.Sig);}
var cj := canonical_judgement(i,phi,B);
match phii																					 
  case Atom(R,par) => //assert is_derivable(cj,phi,B);
  case And(phi0,phi1) 
	 => var j0' := canonical_judgement(i+[0],phi,B);
		var j1' := canonical_judgement(i+[1],phi,B);
		var j0 := J(i, j0'.V, j0'.F);
		var j1 := J(i, j1'.V, j1'.F); 
		canonical_judgement_Lemma(i+[0],phi,B);
		canonical_judgement_Lemma(i+[1],phi,B);
		setofValmodelsAnd_Lemma(phi0, phi1, B);
		assert  cj.F == setOfValmodels(phii,B);	
		assert is_derivable(j0,phi,B) && is_derivable(j1,phi,B); 
		//assert is_derivable(cj,phi,B);						
  case Forall(x,beta) 
     => var j0 := canonical_judgement(i+[0],phi,B);
		canonical_judgement_Lemma(i+[0],phi,B);
		if x !in j0.V {
			forall f:Valuation<T> | f.Values <= B.Dom
			            { NoFreeVarInForall_Lemma(B,f,x,beta); }
			assert cj.F == setOfValmodels(beta,B) == setOfValmodels(Forall(x, beta), B);	
			//assert is_derivable(cj,phi,B);
	    } else {
			assert cj == dualProjection(x,j0,phi,B);
			setofValmodelsForall_Lemma(x, beta, B);
			assert cj.F == setOfValmodels(Forall(x,beta),B);		
			//assert is_derivable(cj,phi,B);
		}                      
case Exists(x,beta) 
   => var j0 := canonical_judgement (i+[0],phi,B);
	  canonical_judgement_Lemma(i+[0],phi,B);
	  if x !in j0.V {
			forall f:Valuation<T> | f.Values <= B.Dom
					{ NoFreeVarInExists_Lemma(B,f,x,beta); }
			assert setOfValmodels(beta,B) == setOfValmodels(Exists(x, beta), B);	
			assert cj.F == setOfValmodels(beta,B);
			//assert is_derivable(cj,phi,B);
		} else { 
			var jp :=  projection(j0, j0.V-{x},phi,B);
			assert cj == J(i, jp.V, jp.F);
			assert cj.F == (set h | h in setOfValmodels(beta,B) :: projectVal(h,j0.V-{x}));
			setofValmodelsExists_Lemma(x,beta,B); 
			assert  setOfValmodels(Exists(x,beta),B) 
			        == (set h | h in setOfValmodels(beta,B) :: projectVal(h,j0.V-{x}));
			assert cj.F == setOfValmodels(Exists(x,beta),B);           
			assert is_derivable(j0,phi,B); 
			//assert is_derivable(cj,phi,B);
		}  
}

lemma completeness_Theorem<T> (phi:Formula,B:Structure<T>)
  requires wfQCSP_Instance(phi,B)
  requires !models(B,map[],phi) 
  ensures is_derivable(J([],{},{}),phi,B) 
{
if !is_derivable(J([],{},{}),phi,B)
	{
	var cj :| cj == canonical_judgement([],phi,B);
	canonical_judgement_Lemma([], phi, B);
	//assert cj.F == (set f:Valuation<T> | f in allMaps({}, B.Dom) 
	//                                     && models(B,f,phi)) != {};
	//assert cj.F == {map[]};
	//assert models(B,map[],phi);
    }
}
} 