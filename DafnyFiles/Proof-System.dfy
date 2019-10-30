include "QCSP-Instance.dfy"

module Proof_System { 
    import opened Utils 
	import opened QCSP_for_PS = QCSP_Instance`Defs_for_Proof_System
	export Lemma_and_Defs 
	        provides Utils, QCSP_for_PS, indexSubformula_Lemma
	        reveals Index, Judgement, wfJudgement, setOfIndex, FoI, 
			        is_projection, is_join, is_dualProjection, is_upwardFlow,
					is_derivable

type Index = seq<int>

function setOfIndex(phi:Formula): set<Index>
{
match phi
	case Atom(R,par) => { [] }
	case And(phi,psi) => { [] } + (set s | s in setOfIndex(phi) :: [0]+s) 
								+ (set s | s in setOfIndex(psi) :: [1]+s) 
	case Forall(x,phi) => { [] } + (set s | s in setOfIndex(phi) :: [0]+s)
	case Exists(x,phi) => { [] } + (set s | s in setOfIndex(phi) :: [0]+s)
}

function method FoI(s:Index, phi:Formula, Sig:Signature): Formula
    requires s in setOfIndex(phi)
    ensures subformula(FoI(s,phi,Sig), phi)
    ensures FoI(s,phi,Sig) < phi <==> s != []
    ensures wfFormula(Sig,phi) ==> wfFormula(Sig,FoI(s,phi,Sig))
{
if  s == [] then phi
else // assert !(phi.Atom?);
		match phi
				case And(phi,psi) => if s[0] == 0 then FoI(s[1..],phi,Sig) 
				                                  else FoI(s[1..],psi,Sig) 
				case Forall(x,phi) => FoI(s[1..],phi,Sig) 
				case Exists(x,phi) => FoI(s[1..],phi,Sig) 
}

// Lemmas relating indexes with formulae and subformulae

lemma Index_Lemma(alpha:Formula, phi:Formula, s:Index, Sig:Signature)
	requires s in setOfIndex(phi) && FoI(s,phi,Sig) == alpha
	requires alpha != phi
	ensures phi.And? ==>  s != [] 
						  && ((subformula(alpha,phi.0) && s[0] == 0 && s[1..] in setOfIndex(phi.0) && FoI(s[1..],phi.0,Sig) == alpha)
							  || (subformula(alpha,phi.1) && s[0] == 1 && s[1..] in setOfIndex(phi.1) && FoI(s[1..],phi.1,Sig) == alpha))
	ensures phi.Forall? ==> s != []  
							&& subformula(alpha,phi.Body) && s[0] == 0 && s[1..] in setOfIndex(phi.Body) && FoI(s[1..],phi.Body,Sig) == alpha
	ensures phi.Exists? ==> s != []  
							&& subformula(alpha,phi.Body) && s[0] == 0 && s[1..] in setOfIndex(phi.Body) && FoI(s[1..],phi.Body,Sig) == alpha
{
if phi.And? {
	assert subformula(alpha,phi.0) || subformula(alpha,phi.1);
	assert alpha == if s[0] == 0 then FoI(s[1..],phi.0,Sig) else FoI(s[1..],phi.1,Sig); 
	}
// The two other cases are automatically proved
}

lemma IndexSum_Lemma(phi:Formula, alpha:Formula, beta:Formula, r1:Index, r2:Index, Sig:Signature)
	requires r1 in setOfIndex(phi) && FoI(r1,phi,Sig) == alpha 
	requires r2 in setOfIndex(alpha) && FoI(r2,alpha,Sig) == beta
	ensures r1+r2 in setOfIndex(phi) && FoI(r1+r2,phi,Sig) == beta
	decreases r1
{
assert r1 != [] ==> r1+r2 == ([r1[0]]+r1[1..])+r2 == [r1[0]]+(r1[1..]+r2);	
if alpha == phi { 
   assert r1 == [] && r1+r2 == r2;
} else if phi.And? { 
	   Index_Lemma(alpha,phi,r1,Sig);
	   assert (subformula(alpha,phi.0) && r1[0] == 0 && r1[1..] in setOfIndex(phi.0) && FoI(r1[1..],phi.0,Sig) == alpha)
			|| (subformula(alpha,phi.1) && r1[0] == 1 && r1[1..] in setOfIndex(phi.1) && FoI(r1[1..],phi.1,Sig) == alpha);
	   if subformula(alpha,phi.0) && r1[0] == 0 && r1[1..] in setOfIndex(phi.0) && FoI(r1[1..],phi.0,Sig) == alpha { 
			IndexSum_Lemma(phi.0, alpha, beta, r1[1..], r2, Sig); 
			assert r1[1..]+r2 in setOfIndex(phi.0) && FoI(r1[1..]+r2, phi.0, Sig) == beta;
			assert [0]+(r1[1..]+r2) in setOfIndex(phi);	
		} else {
			assert subformula(alpha,phi.1) && r1[0] == 1 && r1[1..] in setOfIndex(phi.1) && FoI(r1[1..],phi.1,Sig) == alpha;
			IndexSum_Lemma(phi.1, alpha, beta, r1[1..], r2, Sig); 
			assert r1[1..]+r2 in setOfIndex(phi.1) && FoI(r1[1..]+r2, phi.1, Sig) == beta;
			assert [1]+(r1[1..]+r2) in setOfIndex(phi);
			}
		assert r1+r2 in setOfIndex(phi);
		assert FoI(r1+r2,phi,Sig) == beta;
} else { // assert phi.Forall? || phi.Exists?;
		Index_Lemma(alpha,phi,r1,Sig);
		assert (subformula(alpha,phi.Body) && r1[0] == 0 && r1[1..] in setOfIndex(phi.Body) && FoI(r1[1..],phi.Body,Sig) == alpha);
		IndexSum_Lemma(phi.Body,alpha,beta,r1[1..],r2,Sig);                           
		assert r1[1..]+r2 in setOfIndex(phi.Body) && FoI(r1[1..]+r2,phi.Body,Sig) == beta;
		assert [0]+(r1[1..]+r2) in setOfIndex(phi);
		assert r1+r2 in setOfIndex(phi);
		assert FoI(r1+r2,phi,Sig) == beta;
}
}

lemma indexSubformula_Lemma (s:Index, phi:Formula, Sig:Signature)
	requires s in setOfIndex(phi) && !FoI(s,phi,Sig).Atom?
	ensures FoI(s,phi,Sig).And?  ==> s+[0] in setOfIndex(phi) && FoI(s,phi,Sig).0 == FoI(s+[0],phi,Sig) 
									&& s+[1] in setOfIndex(phi) && FoI(s,phi,Sig).1 == FoI(s+[1],phi,Sig)
	ensures FoI(s,phi,Sig).Forall? ==> s+[0] in setOfIndex(phi) && FoI(s,phi,Sig).Body == FoI(s+[0],phi,Sig) 
									&& freeVar(FoI(s,phi,Sig)) == freeVar(FoI(s+[0],phi,Sig))-{FoI(s,phi,Sig).x}
	ensures FoI(s,phi,Sig).Exists? ==>  s+[0] in setOfIndex(phi) && FoI(s,phi,Sig).Body == FoI(s+[0],phi,Sig) 
									&& freeVar(FoI(s,phi,Sig)) == freeVar(FoI(s+[0],phi,Sig))-{FoI(s,phi,Sig).x}
{
var phis := FoI(s,phi,Sig);
if phis.And? { 
			// phis.0
			assert (set s | s in setOfIndex(phis.0) :: [0]+s) <= setOfIndex(phis);
			// assert [0]+[] in  setOfIndex(phis);
			assert [0] == [0]+[];
			// assert [0] in  setOfIndex(phis);
			assert FoI([0],phis,Sig) == phis.0;
			IndexSum_Lemma(phi,phis,phis.0,s,[0],Sig);
			assert s+[0] in setOfIndex(phi) && FoI(s+[0],phi,Sig) == FoI(s,phi,Sig).0;
			// phis.1
			assert (set s | s in setOfIndex(phis.1) :: [1]+s) <= setOfIndex(phis);
			// assert [1]+[] in  setOfIndex(phis);
			assert [1] == [1]+[];
			//assert [1] in  setOfIndex(phis);
			assert FoI([1],phis,Sig) == phis.1;
			IndexSum_Lemma(phi,phis,phis.1,s,[1],Sig);
			assert s+[1] in setOfIndex(phi) && FoI(s+[1],phi,Sig) == FoI(s,phi,Sig).1;
			}
else if phis.Forall? {
					assert (set s | s in setOfIndex(phis.Body) :: [0]+s) <= setOfIndex(phis);
					// assert [0]+[] in  setOfIndex(phis);
					assert [0] == [0]+[];
					// assert [0] in  setOfIndex(phis);
					assert FoI([0],phis,Sig) == phis.Body;
					IndexSum_Lemma(phi,phis,phis.Body,s,[0],Sig);
					assert s+[0] in setOfIndex(phi) && FoI(s+[0],phi,Sig) == FoI(s,phi,Sig).Body;
					}
else if phis.Exists? {  
					assert (set s | s in setOfIndex(phis.Body) :: [0]+s) <= setOfIndex(phis);
					// assert [0]+[] in  setOfIndex(phis);
					assert [0] == [0]+[];
					// assert [0] in  setOfIndex(phis);
					assert FoI([0],phis,Sig) == phis.Body;
					IndexSum_Lemma(phi,phis,phis.Body,s,[0],Sig);
					assert s+[0] in setOfIndex(phi) && FoI(s+[0],phi,Sig) == FoI(s,phi,Sig).Body;
					}
}

lemma setOfIndexSuffix_Lemma(s:Index, phi:Formula, Sig:Signature)
	requires s in setOfIndex(phi) 
	ensures !FoI(s,phi,Sig).Atom? ==> s+[0] in setOfIndex(phi) 
	ensures FoI(s,phi,Sig).And? ==> s+[1] in setOfIndex(phi)
{
if !FoI(s,phi,Sig).Atom? { indexSubformula_Lemma(s,phi,Sig);}
}

// Judgements

datatype Judgement<T(==)> = J(i:Index,V:set<Name>,F:set<Valuation<T>>)

predicate wfJudgement<T> (j:Judgement<T>,phi:Formula,B:Structure<T>)
// j is a well-formed judgement on a well-formed QCSP instance (phi,B)
{
wfQCSP_Instance(phi,B)            
&&
j.i in setOfIndex(phi)
&& 
j.V <= freeVar(FoI(j.i,phi,B.Sig))
&&
(forall f :: f in j.F ==> j.V == f.Keys)
&&
(forall f, v :: f in j.F ==> v in f.Values ==> v in B.Dom)
}


predicate is_projection<T> (j1:Judgement<T>, j2:Judgement<T>, phi:Formula,
                            B:Structure<T>)
	// j1 is a projection of j2
	requires wfJudgement(j1,phi,B) && wfJudgement(j2,phi,B)
{
j1.i == j2.i &&
j1.V <= j2.V &&											
j1.F == ( set f | f in j2.F :: projectVal(f,j1.V) ) 
}

predicate is_join<T> (j:Judgement<T>, j1:Judgement<T>, j2:Judgement<T>,
                      phi:Formula, B:Structure<T>)
	requires wfJudgement(j,phi,B) && wfJudgement(j1,phi,B) && wfJudgement(j2,phi,B)
{
j.i == j1.i == j2.i &&
j.V == j1.V + j2.V &&
j.F == (set f:Valuation<T> | f in allMaps(j1.V+j2.V, B.Dom)
                             && projectVal(f,j1.V) in j1.F 
                             && projectVal(f,j2.V) in j2.F)
}

predicate is_dualProjection<T> (j1:Judgement<T>,v:Name,j2:Judgement<T>,phi:Formula,
                                B:Structure<T>)
	// j1 is a dual projection of j2
	requires wfJudgement(j1,phi,B) && wfJudgement(j2,phi,B)  
{
j2.i == j1.i + [0] &&
j1.V == j2.V - {v} &&
v in j2.V &&
j1.F == (set h:Valuation<T> | h in allMaps(j1.V, B.Dom)
                              && forall b :: b in B.Dom ==> h[v:=b] in j2.F) 
}

predicate is_upwardFlow<T> (j1:Judgement<T>, j2:Judgement<T>, phi:Formula,
                            B:Structure<T>)
	// j1 is the upwardFlow of j2
	requires wfJudgement(j1,phi,B) && wfJudgement(j2,phi,B)
{
j2.V == j1.V && j2.F == j1.F &&
(
( FoI(j1.i,phi,B.Sig).And? && (j2.i == j1.i+[0] || j2.i == j1.i+[1]) )
||
( (FoI(j1.i,phi,B.Sig).Forall? || FoI(j1.i,phi,B.Sig).Exists?) && j2.i == j1.i+[0] )

)
}

// Proof System
inductive predicate is_derivable<T(!new)> (j:Judgement<T>, phi:Formula, B:Structure<T>)
	requires wfQCSP_Instance(phi,B) && wfJudgement(j,phi,B) 
{
var phii := FoI(j.i,phi,B.Sig);
( // by rule (atom)
phii.Atom? 
&& j.V == setOf(phii.par) 
&& j.F == (set f:Valuation<T> | f in allMaps(j.V, B.Dom)
                                && HOmap(f,phii.par) in B.I[phii.rel])
) 
||
( // by rule (projection)
exists j' :: wfJudgement(j',phi,B) 
            && is_projection(j,j',phi,B)  
			&& is_derivable(j',phi,B) 
) 
||
( // by rule (join)
phii.And? 
&& exists j0,j1 :: wfJudgement(j0,phi,B) && wfJudgement(j1,phi,B) && j0.i == j1.i  
                    && is_join(j,j0,j1,phi,B) 
                    && is_derivable(j0,phi,B)  && is_derivable(j1,phi,B) 
) 
||
( // by rule (∀-elimination)
phii.Forall? 
&& exists j' :: wfJudgement(j',phi,B) 
                && phii == Forall(phii.x,FoI(j'.i,phi,B.Sig)) 
				&& is_dualProjection(j,phii.x,j',phi,B)
				&& is_derivable(j',phi,B) 
) 
||
( // by rule (upward flow)
!phii.Atom? && exists j' :: wfJudgement(j',phi,B)  
			               && is_upwardFlow(j,j',phi,B)
			               && is_derivable(j',phi,B) 
) 
}

} 