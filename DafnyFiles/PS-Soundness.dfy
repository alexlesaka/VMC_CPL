include "Conjunctive-Pos-Logic.dfy"
include "Proof-System.dfy"

module PS_Soundness {
	import opened Utils
	import opened QCSP_Instance`Lemmas_for_PS_Soundness
    import opened Conjunctive_Pos_Logic`Lemmas_for_PS_Soundness
	import opened Proof_System`Lemma_and_Defs

predicate valuationModel<T> (h:Valuation<T>, j:Judgement<T>, phi:Formula, B:Structure<T>) 
{
h in allMaps(j.V, B.Dom) 
&& wfStructure(B) && wfFormula(B.Sig, phi) && wfJudgement(j, phi, B) 
&& models(B,h,existSq(freeVar(FoI(j.i,phi,B.Sig))-j.V,FoI(j.i,phi,B.Sig)))
}

lemma projection_Lemma<T>(j:Judgement<T>, j':Judgement<T>, phi:Formula, B:Structure<T>) 
	requires wfStructure(B) && wfFormula(B.Sig,phi) && wfJudgement(j,phi,B) && wfJudgement(j',phi,B)
	requires is_projection(j,j',phi,B) 
	requires wfFormula(B.Sig,existSq(freeVar(FoI(j'.i,phi,B.Sig))-j'.V,FoI(j'.i,phi,B.Sig))) 
	requires forall h :: valuationModel(h,j',phi,B)  ==> h in j'.F
	ensures wfFormula(B.Sig,existSq(freeVar(FoI(j.i,phi,B.Sig))-j.V,FoI(j.i,phi,B.Sig))) 
	ensures forall h :: valuationModel(h,j,phi,B) ==> h in j.F
{
var phii := FoI(j.i,phi,B.Sig);
var W := freeVar(phii)-j'.V;
var Y := j'.V - j.V;		
var X := freeVar(phii)-j.V;
forall h:Valuation<T> | valuationModel(h,j,phi,B) 
	ensures h in j.F;
	{ 
	assert  models(B,h,existSq(X,phii));
	assert X == Y+W;
	assert models(B,h,existSq(Y+W,phii)); 
	existSq_Sum_Lemma(B, h, Y, W, phii); 						
	assert models(B,h,existSq(Y,existSq(W,phii))); 
	assert models(B,h,existSq(Y,existSq(W,phii)));
	existSqSem_Lemma(B, h, Y, existSq(W,phii));  
	var U, Z :| setOf(Z) <= B.Dom && |U| == |Z| == |Y| && setOf(U) == Y
							&& noDups(U) && setOf(U) !! h.Keys
							&& extVal(h,U,Z).Values <= B.Dom
							&& models(B,extVal(h,U,Z),existSq(W,phii));
	extValDomRange_Lemma(h, U, Z); 
	assert extVal(h,U,Z).Keys == h.Keys + setOf(U);
	assert j.V + (j'.V-j.V) == j'.V;
	assert extVal(h,U,Z).Keys == j'.V;
	extValallMaps_Lemma(h, U, Z, B);
	assert extVal(h,U,Z) in allMaps(j'.V, B.Dom);
	assert extVal(h,U,Z) in j'.F;
	assert h.Keys == j.V;
	projectOfExtVal_Lemma(h, U, Z); 					  
	assert projectVal(extVal(h,U,Z),j.V) == h;  
	assert j.F == ( set f | f in j'.F :: projectVal(f,j.V) );
	assert h in j.F;
	} 
}

lemma join_Lemma<T> (j:Judgement<T>, j1:Judgement<T>, j2:Judgement<T>, phi:Formula, B:Structure<T>) 
	requires wfStructure(B) && wfFormula(B.Sig,phi) 
	requires wfJudgement(j,phi,B) && wfJudgement(j1,phi,B) && wfJudgement(j2,phi,B) && j1.i == j2.i
	requires wfFormula(B.Sig,existSq(freeVar(FoI(j1.i,phi,B.Sig))-j1.V,FoI(j1.i,phi,B.Sig))) 
	requires forall h :: valuationModel(h,j1,phi,B) ==> h in j1.F
	requires wfFormula(B.Sig,existSq(freeVar(FoI(j1.i,phi,B.Sig))-j2.V,FoI(j2.i,phi,B.Sig)))
	requires forall h :: valuationModel(h,j2,phi,B) ==> h in j2.F
	requires is_join(j,j1,j2,phi,B) 
	ensures wfFormula(B.Sig,existSq(freeVar(FoI(j.i,phi,B.Sig))-j.V,FoI(j.i,phi,B.Sig))) 
	ensures forall h :: valuationModel(h,j,phi,B) ==> h in j.F
{
var phii := FoI(j.i,phi,B.Sig);
var W := freeVar(phii)-(j1.V+j2.V);
var W1 := freeVar(phii)-j1.V;
var W2 := freeVar(phii)-j2.V;
forall h | valuationModel(h,j,phi,B)
	ensures h in j.F; 
	{ 
	assert h in allMaps(j1.V+j2.V, B.Dom) && models(B,h,existSq(W,phii));
	ProyectMap_Lemma(h, j1.V, j1.V+j2.V, B.Dom);
	assert projectVal(h,j1.V) in allMaps(j1.V, B.Dom);
	ProyectMap_Lemma(h, j2.V, j1.V+j2.V, B.Dom);
	assert projectVal(h,j2.V) in allMaps(j2.V, B.Dom);
	ExistsProject_Lemma(B, h, j1.V, phii); 
	assert models(B,projectVal(h,j1.V),existSq(W1,phii));
	ExistsProject_Lemma(B, h, j2.V, phii); 
	assert models(B,projectVal(h,j2.V),existSq(W2,phii));
	assert valuationModel(projectVal(h,j1.V),j1,phi,B)  
		   && valuationModel(projectVal(h,j2.V),j2,phi,B);
	assert projectVal(h,j1.V) in j1.F && projectVal(h,j2.V) in j2.F;
	assert h in j.F;
}
}

lemma dualProjection_Lemma<T> (j:Judgement<T>,j':Judgement<T>,phi:Formula,B:Structure<T>) 
	requires wfStructure(B) && wfFormula(B.Sig,phi) && wfJudgement(j,phi,B) && wfJudgement(j',phi,B) 
	requires FoI(j.i,phi,B.Sig).Forall? && FoI(j.i,phi,B.Sig).x in j'.V
	         && FoI(j.i,phi,B.Sig) == Forall(FoI(j.i,phi,B.Sig).x,FoI(j'.i,phi,B.Sig)) 
			 && j'.i == j.i+[0]  && j.V == j'.V -{FoI(j.i,phi,B.Sig).x}  
	requires wfFormula(B.Sig,existSq(freeVar(FoI(j'.i,phi,B.Sig))-j'.V,FoI(j'.i,phi,B.Sig))) 
	requires forall h :: valuationModel(h,j',phi,B) ==> h in j'.F
	requires is_dualProjection(j, FoI(j.i,phi,B.Sig).x, j', phi, B) 
	ensures wfFormula(B.Sig,existSq(freeVar(FoI(j.i,phi,B.Sig))-j.V,FoI(j.i,phi,B.Sig))) 
	ensures forall h :: valuationModel(h,j,phi,B) ==> h in j.F
{
var phii := FoI(j.i,phi,B.Sig);   
var phik := FoI(j'.i,phi,B.Sig);  
var y := FoI(j.i,phi,B.Sig).x;
assert phii == Forall(y,phik);			
var W := freeVar(phii)-j.V;
assert y !in W;
var W' := freeVar(phik)-j'.V;
forall h:Valuation<T>, v:T |  valuationModel(h,j,phi,B)  && v in B.Dom
	ensures h in allMaps(j.V, B.Dom) && h[y:=v] in j'.F 
	{  
	assert h.Keys == j'.V-{y}  && h.Values <= B.Dom  && models(B,h,existSq(W,phii));
	existSqSem_Lemma(B, h, W, phii); 
	var U,V :| setOf(V) <= B.Dom  && |U| == |V| == |W|  && setOf(U) == W && noDups(U)
		&& setOf(U) !! h.Keys
		&& extVal(h,U,V).Values <= B.Dom
		&& models(B,extVal(h,U,V),phii);
	assert models(B,extVal(h,U,V)[y:=v],phik);
	assert y !in U;  
	extValCommute_Lemma(y,v,h,U,V);
	assert extVal(h,U,V)[y:=v] == extVal(h[y:=v],U,V);
	assert extVal(h[y:=v],U,V).Values <= B.Dom;	
	assert models(B,extVal(h[y:=v],U,V),phik);
	assert h[y:=v].Keys == j'.V == freeVar(phik) - W';			
	existSq_ExtVal_Lemma(B, h[y:=v], U, V, W', phik);
	assert models(B,h[y:=v],existSq(W',phik));
	assert j.V == j'.V-{y};
	ExtMap_Lemma(h, y, v, j'.V, B.Dom);
	assert h[y:=v] in allMaps(j'.V, B.Dom);
	assert valuationModel(h[y:=v],j',phi,B);
	assert h[y:=v] in j'.F;
    }
assert forall h:Valuation<T>, v:T :: (valuationModel(h,j,phi,B)  && v in B.Dom) 
               ==> (h in allMaps(j.V, B.Dom) && h[y:=v] in j'.F);
assert forall h:Valuation<T> :: valuationModel(h,j,phi,B) ==> h in j.F;
}

lemma upArrowExists_Lemma<T> (j:Judgement<T>,j':Judgement<T>,phi:Formula,B:Structure<T>) 
	requires wfStructure(B) && wfFormula(B.Sig,phi) 
	requires wfJudgement(j,phi,B) && wfJudgement(j',phi,B) 
	requires j.V == j'.V && j.F ==j'.F && j'.i == j.i +[0]
	requires wfFormula(B.Sig,existSq(freeVar(FoI(j'.i,phi,B.Sig))-j'.V,FoI(j'.i,phi,B.Sig))) 
	requires FoI(j.i,phi,B.Sig).Exists? && FoI(j.i,phi,B.Sig) == Exists(FoI(j.i,phi,B.Sig).x, FoI(j'.i,phi,B.Sig));
	requires forall h :: valuationModel(h,j',phi,B) ==> h in j'.F
	ensures wfFormula(B.Sig,existSq(freeVar(FoI(j.i,phi,B.Sig))-j.V,FoI(j.i,phi,B.Sig))) 
	ensures forall h :: valuationModel(h,j,phi,B) ==> h in j.F
{
var phii := FoI(j.i,phi,B.Sig);
var subphi := FoI(j'.i,phi,B.Sig);
var y := FoI(j.i,phi,B.Sig).x;
if y in freeVar(subphi)
{	
forall h | valuationModel(h,j,phi,B)
	{ calc ==> {
			   valuationModel(h,j,phi,B);
		       models(B,h,existSq( freeVar(phii)-j.V,Exists(y,subphi)));
			   models(B,h,existSq( freeVar(phii)-j.V,existSq({y}, subphi)));
	                { existSq_Sum_Lemma (B, h, freeVar(phii)-j.V, {y}, subphi); }
			   models(B,h,existSq( freeVar(phii)-j.V+{y},subphi));
			        { assert freeVar(phii)-j.V + {y} == freeVar(subphi)-j'.V; }
			   h.Keys == j'.V  && h.Values <= B.Dom  && models(B,h,existSq(freeVar(subphi)-j'.V,subphi)); 
		       valuationModel(h,j',phi,B);
			   h in j'.F;
			   h in j.F;
	}}	
} else { 
       forall h | valuationModel(h,j,phi,B)
		{ calc ==> {
				   valuationModel(h,j,phi,B);
						{
						assert freeVar(phii)-j.V == freeVar(subphi)-j'.V;
						existSq_Exists_Commutes_Lemma(B, h, y, freeVar(subphi)-j'.V, subphi);
						}
					h.Keys == j'.V  && h.Values <= B.Dom  && models(B,h,Exists(y, existSq(freeVar(subphi)-j'.V,subphi))); 
						{ NoFreeVarInExists_Lemma(B, h, y, existSq(freeVar(subphi)-j'.V,subphi)); }
					valuationModel(h,j',phi,B);
					h in j.F;
}}}
}

lemma upArrowForall_Lemma<T> (j:Judgement<T>,j':Judgement<T>,phi:Formula,B:Structure<T>) 
	requires wfStructure(B) && wfFormula(B.Sig,phi) 
	requires wfJudgement(j,phi,B) && wfJudgement(j',phi,B) 
	requires j.V == j'.V && j.F ==j'.F && j'.i == j.i +[0]
	requires wfFormula(B.Sig,existSq(freeVar(FoI(j'.i,phi,B.Sig))-j'.V,FoI(j'.i,phi,B.Sig))) 
	requires FoI(j.i,phi,B.Sig).Forall? && FoI(j.i,phi,B.Sig) == Forall(FoI(j.i,phi,B.Sig).x, FoI(j'.i,phi,B.Sig));
	requires forall h :: valuationModel(h,j',phi,B) ==> h in j'.F
	ensures wfFormula(B.Sig,existSq(freeVar(FoI(j.i,phi,B.Sig))-j.V,FoI(j.i,phi,B.Sig))) 
	ensures forall h :: valuationModel(h,j,phi,B) ==> h in j.F
{
var phii := FoI(j.i,phi,B.Sig);
var subphi := FoI(j'.i,phi,B.Sig);
var x := FoI(j.i,phi,B.Sig).x;
if x in freeVar(subphi) {
	forall h | valuationModel(h,j,phi,B)
	{ calc ==> {
	            h.Keys == j'.V && h.Values <= B.Dom && models(B,h,existSq(freeVar(Forall(x,subphi))-j'.V,Forall(x,subphi)));
			        { existSq_Forall_Lemma(B, h, x, freeVar(Forall(x,subphi))-j'.V, subphi); }
				h.Keys == j'.V && h.Values <= B.Dom && models(B,h,existSq(freeVar(Exists(x,subphi))-j'.V,Exists(x,subphi)));
			    models(B,h,existSq(freeVar(phii)-j.V,Exists(x,subphi)));
                   // {wff_existSq_Lemma(B.Sig,{x},subphi);}
				models(B,h,existSq(freeVar(phii)-j.V,existSq({x}, subphi)));
                    {existSq_Sum_Lemma (B, h, freeVar(phii)-j.V, {x}, subphi);}
				models(B,h,existSq(freeVar(phii)-j.V+{x},subphi));
                    {assert freeVar(phii)-j.V + {x} == freeVar(subphi)-j'.V;}
				h.Keys == j'.V  && h.Values <= B.Dom  && models(B,h,existSq(freeVar(subphi)-j'.V,subphi)); 
                valuationModel(h,j',phi,B);
                h in j'.F;
                h in j.F;
	}}	
} else {
	forall h | valuationModel(h,j,phi,B)
	{ calc ==> {
			   h.Keys == j'.V && h.Values <= B.Dom && models(B,h,existSq(freeVar(Forall(x,subphi))-j'.V,Forall(x,subphi)));
                   { existSq_Forall_Lemma(B,h,x,freeVar(Forall(x,subphi))-j'.V,subphi); }
			   h.Keys == j'.V && h.Values <= B.Dom && models(B,h,existSq(freeVar(Exists(x,subphi))-j'.V,Exists(x,subphi)));
				   { 
				   assert freeVar(phii)-j.V == freeVar(subphi)-j'.V;
				   existSq_Exists_Commutes_Lemma(B, h, x, freeVar(subphi)-j'.V, subphi);
				   }
			   h.Keys == j'.V  && h.Values <= B.Dom  && models(B,h,Exists(x, existSq(freeVar(subphi)-j'.V,subphi))); 
                   { NoFreeVarInExists_Lemma(B, h, x, existSq(freeVar(subphi)-j'.V,subphi)); }
			   valuationModel(h,j',phi,B);
               h in j.F;
	}}
}
}

lemma upArrowAnd_Lemma<T> (j:Judgement<T>,j':Judgement<T>,phi:Formula,B:Structure<T>) 
	requires j'.i in setOfIndex(phi);
	requires wfStructure(B) && wfFormula(B.Sig,phi) && wfFormula(B.Sig, FoI(j'.i,phi,B.Sig))
	requires wfJudgement(j,phi,B) && wfJudgement(j',phi,B)
	requires j.V == j'.V && j.F ==j'.F && (j'.i == (j.i +[0]) || j'.i==(j.i+[1]))
	requires wfFormula(B.Sig,existSq(freeVar(FoI(j'.i,phi,B.Sig))-j'.V,FoI(j'.i,phi,B.Sig))) ;
	requires FoI(j.i,phi,B.Sig).And? && (FoI(j'.i,phi,B.Sig) == FoI(j.i,phi,B.Sig).0 || FoI(j'.i,phi,B.Sig) == FoI(j.i,phi,B.Sig).1); 
	requires forall h :: valuationModel(h,j',phi,B) ==> h in j'.F
	ensures wfFormula(B.Sig,existSq(freeVar(FoI(j.i,phi,B.Sig))-j.V,FoI(j.i,phi,B.Sig))) 
	ensures forall h :: valuationModel(h,j,phi,B) ==> h in j.F
{
var phii := FoI(j.i,phi,B.Sig);
var subphi := FoI(j'.i,phi,B.Sig);
assert phii.0 == subphi || phii.1 == subphi;
var W := freeVar(phii)-j.V;
forall h | valuationModel(h,j,phi,B) ensures h in j.F
	{ 
	assert h.Keys == j.V  && h.Values <= B.Dom  
	       && models(B,h,existSq(W,phii));
	assert freeVar(existSq(W,phii)) <= j.V == h.Keys;
    existSq_Distr_And_Lemma(B, h, W, phii);
	/* assert wfFormula(B.Sig,existSq(W*freeVar(phii.0),phii.0))
			&& wfFormula(B.Sig,existSq(W*freeVar(phii.1),phii.1))
			&& models(B,h,existSq(W*freeVar(phii.0),phii.0))
			&& models(B,h,existSq(W*freeVar(phii.1),phii.1));*/ 
	var W0 := W*freeVar(phii.0);
	// assert W0 == freeVar(phii.0)-j'.V;
	var W1 := W*freeVar(phii.1);
	// assert W1 == freeVar(phii.1)-j'.V;
	var W' := if subphi == phii.0 then W0 else W1;
	assert W' == freeVar(subphi)-j'.V;
	assert h.Keys == j'.V  && h.Values <= B.Dom  
	            && models(B,h,existSq(W',subphi));    
	assert h.Keys == j'.V  && h.Values <= B.Dom 
	            && models(B,h,existSq(freeVar(subphi)-j'.V,subphi));
	assert valuationModel(h,j',phi,B);
	assert h in j'.F;
	assert h in j.F;
	}	
}

inductive lemma models_Lemma<T> (j:Judgement<T>, phi:Formula, B:Structure<T>) 
	requires wfQCSP_Instance(phi, B) && wfJudgement(j, phi, B) 
	requires is_derivable(j,phi,B)				
	//ensures wfFormula(B.Sig, existSq(freeVar(FoI(j.i,phi,B.Sig))-j.V, FoI(j.i,phi,B.Sig)))  //ATENCION
	ensures forall h :: valuationModel(h,j,phi,B) ==> h in j.F
{
var phii := FoI(j.i, phi,B.Sig);
if phii.Atom?  && j.V == setOf(phii.par) 
   && j.F == (set f: Valuation<T> | 
					  f in allMaps(j.V, B.Dom) 
                      && HOmap(f,phii.par) in B.I[phii.rel]) { 
   // Atom 
   forall h | valuationModel(h,j,phi,B) { allMaps_Correct_Lemma(h, B.Dom); }
} else if exists j' :: wfJudgement(j',phi,B) && is_projection(j,j',phi,B)  && is_derivable(j',phi,B) { 
   // Projection 
   var j' :| wfJudgement(j',phi,B) && is_projection(j,j',phi,B)  
             && is_derivable(j',phi,B);
   models_Lemma(j',phi,B); 
   projection_Lemma(j,j',phi,B);
} else if phii.And? && exists j1,j2 :: wfJudgement(j1,phi,B) && wfJudgement(j2,phi,B)  && j1.i == j2.i  && is_join(j,j1,j2,phi,B) 
                                      && is_derivable(j1,phi,B)  && is_derivable(j2,phi,B) { 
   // Join 
   var j1,j2 :|  wfJudgement(j1,phi,B) && wfJudgement(j2,phi,B)  && j1.i == j2.i && is_join(j,j1,j2,phi,B) 
				 && is_derivable(j1,phi,B) && is_derivable(j2,phi,B);
   models_Lemma(j1,phi,B); 
   models_Lemma(j2,phi,B); 
   join_Lemma(j,j1,j2,phi,B);
   }
else if phii.Forall? && exists j' :: wfJudgement(j',phi,B) && phii == Forall(phii.x,FoI(j'.i,phi,B.Sig)) && is_dualProjection(j,phii.x,j',phi,B)
							         && is_derivable(j',phi,B) {
	// ForallElim  
	var j' :| wfJudgement(j',phi,B) && phii == Forall(phii.x,FoI(j'.i,phi,B.Sig)) && is_dualProjection(j,phii.x,j',phi,B)
							         && is_derivable(j',phi,B);
	models_Lemma(j',phi,B);  
	dualProjection_Lemma(j,j',phi,B);  
} else {  
    // UpwardFlow
	assert !phii.Atom? && exists j' :: wfJudgement(j',phi,B) && is_upwardFlow(j,j',phi,B) && is_derivable(j',phi,B);
	var j' :| wfJudgement(j',phi,B) && is_upwardFlow(j,j',phi,B) && is_derivable(j',phi,B);
	models_Lemma(j',phi,B); 
	indexSubformula_Lemma(j.i,phi,B.Sig);
	if phii.And? { 
		upArrowAnd_Lemma(j,j',phi,B);
	} else if phii.Forall?  {
		upArrowForall_Lemma(j,j',phi,B);
	} else {
	    upArrowExists_Lemma(j,j',phi,B);	 
	} 
}
}

lemma soundness_Theorem<T> (phi:Formula,B:Structure<T>)
  requires wfQCSP_Instance(phi,B)
  requires is_derivable(J([],{},{}),phi,B) 
  ensures !models(B,map[],phi)
{
var cj := J([],{},{});
models_Lemma(cj,phi,B); 
assert !valuationModel(map[],cj,phi,B);
  //var epsilon: map<Name,T> := map[];
  //assert allMaps({},B.Dom) == {epsilon};
  //assert !models(B,map[],phi);
}

}