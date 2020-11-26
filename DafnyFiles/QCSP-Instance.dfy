include "Utils.dfy"

module QCSP_Instance {
  import opened Utils
  export Lemmas_for_Conjunctive_Pos_Logic
                reveals Name, Valuation, Structure, Signature, Formula, extVal, 
				        wfStructure, wfFormula, models, freeVar, HOmap, sentence, projectVal
                provides Utils, extValDomRange_Lemma, extValOrder_Lemma, NoFreeVarInExists_Lemma, 
				         Exists_Commutes_Lemma
  export Defs_for_Proof_System 
                provides Utils
				reveals Name, Formula, Signature, Valuation, Structure, subformula, wfFormula,
				        freeVar, projectVal, wfStructure, sentence, wfQCSP_Instance, HOmap
  export Lemmas_for_PS_Soundness 
                provides Utils, extValOrder_Lemma, Exists_Commutes_Lemma, NoFreeVarInExists_Lemma,
				         extValCommute_Lemma, projectOfExtVal_Lemma, extValDomRange_Lemma, 
						 extValallMaps_Lemma
                reveals Name, Valuation, Structure, Signature, Formula, extVal, projectVal, 
				        wfStructure, wfFormula, models, freeVar, HOmap, sentence, wfQCSP_Instance
   export Lemmas_for_PS_Completeness 
                provides Utils, modelsAnd_Lemma, Existsmodels_Lemma, NoFreeVarInExists_Lemma,
				         NoFreeVarInForall_Lemma, extValCommute_Lemma
				reveals Name, Valuation, extVal, Structure, Signature, Formula, projectVal, 
				        HOmap, wfFormula, wfStructure, freeVar, sentence, wfQCSP_Instance, models

type Name = string
// for relation symbols

type Signature =  map<Name, int> 
// A finite set of relation symbols with associated arity

datatype Structure<T> = Structure(Sig:Signature, Dom:set<T>, I: map<Name,set<seq<T>>>)

predicate method wfStructure<T>(B:Structure<T>)
// decides if B is a well formed (defined) structure of signature B.Sig
{
  B.Dom != {} 
  && forall r :: r in B.Sig.Keys ==> ( r in B.I && forall t :: t in B.I[r] ==> |t| == B.Sig[r])
}

datatype Formula =   Atom(rel:Name, par:seq<Name>) 
				   | And(0:Formula, 1:Formula) 
				   | Forall(x:Name, Body:Formula)
                   | Exists(x:Name, Body:Formula)

predicate method wfFormula(S:Signature, phi:Formula)
// decides if phi is a well formed formula of signature S
{
match phi
	case Atom(R, par) => R in S.Keys && |par| == S[R]
	case And(phi0, phi1) => wfFormula(S, phi0) && wfFormula(S, phi1)
	case Forall(x, alpha) => wfFormula(S,alpha)
	case Exists(x, alpha) => wfFormula(S,alpha) 
}

predicate subformula(beta:Formula, phi:Formula)
{
   beta == phi 
|| (beta < phi &&  (     (phi.And? && (subformula(beta, phi.0) || subformula(beta, phi.1))) 
                      || (phi.Forall? && subformula(beta, phi.Body)) 
				      || (phi.Exists? && subformula(beta, phi.Body)) )  ) 
}

function method freeVar(phi:Formula): set<Name>
{
match phi
		case Atom(R, par) => setOf(par)
		case And(ph1, phi1) => freeVar(ph1) + freeVar(phi1)
		case Forall(x, phi) => freeVar(phi) - {x}				
		case Exists(x, phi) => freeVar(phi) - {x}
}

predicate method sentence(phi:Formula)
{
freeVar(phi) == {}
}

predicate method wfQCSP_Instance(phi:Formula, B:Structure)
{
wfStructure(B) && wfFormula(B.Sig,phi) && sentence(phi)
}

type Valuation<T> = map<Name,T>

function method HOmap<U,V>(f: map<U,V>, xs:seq<U> ): seq<V>
	requires setOf(xs) <= f.Keys
	ensures  |HOmap(f,xs)| == |xs|
{  
if xs == [] then [] else [f[xs[0]]] + HOmap(f,xs[1..])
}

function method projectVal<T>(f:Valuation<T>, U:set<Name>): Valuation<T>
	requires U <= f.Keys 
	ensures projectVal(f,U).Keys == U
{
map s | s in U :: f[s]
}

function extVal<T>(f:Valuation<T>, W:seq<Name>, S:seq<T>): Valuation<T>
	requires |W| == |S|
	requires noDups(W)	   
	decreases |W|  
{
if W == [] then f 
           else extVal(f[W[0]:=S[0]],W[1..],S[1..])
}

// Lemmas on Valuations and their extensions and projections.

lemma extValDomRange_Lemma<T>(f:Valuation<T>, W:seq<Name>, S:seq<T>)
	requires |W| == |S|
	requires noDups(W) 
	ensures extVal(f,W,S).Keys == setOf(W) + f.Keys
	ensures extVal(f, W, S).Values <= f.Values + setOf(S)
	decreases W
{
if |W| > 0 { 
   assert f[W[0]:=S[0]].Keys == f.Keys + {W[0]};
   assert f[W[0]:=S[0]].Values <= f.Values + {S[0]};
   extValDomRange_Lemma(f[W[0]:=S[0]], W[1..], S[1..]);
   }
}

lemma extValallMaps_Lemma<T>(f:Valuation<T>, W:seq<Name>, S:seq<T>, B:Structure<T>)
	requires |W| == |S|
	requires noDups(W) && setOf(W) !! f.Keys &&  setOf(S) <= B.Dom
	requires f.Values <= B.Dom
    ensures extVal(f, W, S) in allMaps(extVal(f, W, S).Keys,B.Dom)
{
extValDomRange_Lemma(f, W, S);
allMaps_Correct_Lemma(extVal(f, W, S),B.Dom); 
}

lemma HOmapProject_Lemma<T> (f:Valuation<T>, U:set<Name>, xs:seq<Name>)
	requires setOf(xs) <= U <= f.Keys
	ensures HOmap(projectVal(f,U), xs) == HOmap(f, xs) 
{}

lemma varNotInProjectVal_Lemma<T>(f:Valuation<T>, x:Name, a:T, U:set<Name>)
	requires x !in U
	requires U <= f.Keys
	ensures projectVal(f[x:=a], U) == projectVal(f,U)
{}

lemma ExtVal_Lemma<T>(f:Valuation<T>, U:seq<Name>, Z:seq<T>, x:Name) 
    requires |U| == |Z| && noDups(U) && setOf(U) !! f.Keys
	requires x in f.Keys
	ensures x in extVal(f,U,Z).Keys
	ensures extVal(f,U,Z)[x] == f[x]
	decreases U
{
extValDomRange_Lemma(f, U, Z);
if U != [] { 
    // assert extVal(f,U,Z)[x] == extVal(f[U[0]:=Z[0]],U[1..],Z[1..])[x];
	ExtVal_Lemma(f[U[0]:=Z[0]], U[1..], Z[1..], x);
	// assert f[U[0]:=Z[0]][x] == f[x];
}
}

lemma ExtProjectVal_Lemma<T>(B:Structure<T>, f:Valuation<T>, x:Name, U:set<Name>, v:T)
   requires v in B.Dom && x in U && U <= f.Keys && f[x] == v  
   ensures projectVal(f,U) == projectVal(f,U-{x})[x:=v];
{
var g := (map s | s in U :: f[s]);
var h := (map s | s in U-{x} :: f[s]);
assert (h[x:=v])[x] == f[x];
assert forall s :: s in U-{x} ==> f[s] == (h[x:=v])[s];
assert forall s :: s in U ==> f[s] == (h[x:=v])[s];
assert (projectVal(f,U-{x})[x:=v]).Keys == (U-{x})+{x} == U;
}

lemma projectOfExtVal_Lemma<T>(f:Valuation<T>, U:seq<Name>, Z:seq<T>) 
    requires |U| == |Z| && noDups(U) && setOf(U) !! f.Keys
	ensures f.Keys <= extVal(f,U,Z).Keys
	ensures projectVal(extVal(f,U,Z),f.Keys) == f
{
extValDomRange_Lemma(f, U, Z);
assert  f.Keys <= extVal(f,U,Z).Keys;
forall x | x in f.Keys 
     ensures projectVal(extVal(f,U,Z),f.Keys)[x] == f[x];
	 { calc == {
	  projectVal(extVal(f,U,Z),f.Keys)[x];
	  (map s | s in f.Keys :: extVal(f,U,Z)[s])[x];
	  extVal(f,U,Z)[x];
		{
		ExtVal_Lemma(f, U, Z, x);
		}
	 f[x];
	 }}
}

lemma extValCommute_Lemma<T>(x:Name, v:T, f:Valuation<T>, U:seq<Name>, Z:seq<T>)
	requires |U| == |Z| && noDups(U)
	requires x !in U  
	ensures extVal(f, U, Z)[x:=v] == extVal(f[x:=v], U, Z)	
	decreases |U|
{
  if U != [] {
			  extValCommute_Lemma(x, v, f[U[0]:=Z[0]], U[1..], Z[1..]);
              assert (f[U[0]:=Z[0]])[x:=v] == (f[x:=v])[U[0]:=Z[0]]; 
             }
}

lemma extValOrder_Lemma<T>(k:int, U:seq<Name>, S:seq<T>, f:Valuation<T>)
	requires 0 <= k < |U| == |S|
	requires noDups(U)			
	ensures extVal(f, U, S) 
	        == extVal(f[U[k]:=S[k]], U[..k]+U[k+1..], S[..k]+S[k+1..])
{
  if k == 0 {
  } else {  
         var U' := U[1..k] + U[k+1..];
         var S' := S[1..k] + S[k+1..]; 
         calc {
		      extVal(f, U, S);                       
		      extVal(f[U[0]:=S[0]], U[1..], S[1..]); 
                { 
		        extValOrder_Lemma(k-1, U[1..], S[1..], f[U[0]:=S[0]]);	
		        assert U' == U[1..][..k-1] + U[1..][k..]; 		   
		        assert S' == S[1..][..k-1] + S[1..][k..]; 
		        } 
		      extVal((f[U[0]:=S[0]])[U[k]:=S[k]], U', S');
		        { 
		        assert U[k] != U[0];
		        assert f[U[0]:=S[0]][U[k]:=S[k]] == f[U[k]:=S[k]][U[0]:=S[0]]; 
		        }
		      extVal((f[U[k]:=S[k]])[U[0]:=S[0]], U', S');
		        {
		        assert U[0] !in U';
		        }
		      extVal(f[U[k]:=S[k]], [U[0]]+U', [S[0]]+S');
		        {	
		        assert [U[0]] + U' == U[..k] + U[k+1..];
		        assert [S[0]] + S' == S[..k] + S[k+1..];
		        }
	          extVal(f[U[k]:=S[k]], U[..k]+U[k+1..], S[..k]+S[k+1..]);
              }}
}

lemma extValSum_Lemma<T>(f:Valuation<T>, W:seq<Name>, W':seq<Name>, V:seq<T>, V':seq<T>)
	requires  |W| == |V| &&  |W'| == |V'| && noDups(W) && noDups(W') && noDups(W+W')
	ensures extVal(extVal(f, W, V), W', V') == extVal(f, W+W', V+V')
	decreases |W|
{
  if |W| == 0 { assert W+W' == W' && V+V' == V';
  } else { 
		 assert W[1..] + W' == (W+W')[1..];
		 assert [W[0]] + (W[1..]+W') == W + W' && [V[0]] + (V[1..]+V') == V + V';
		 extValSum_Lemma(f[W[0]:=V[0]], W[1..], W', V[1..], V'); 
		 extValOrder_Lemma(0,W+W',V+V',f);
         } 
}

// The predicate models decides if the (B,f) is a model of phi (in symbols, B,f |= phi)

predicate method models<T>(B:Structure<T>, f:Valuation<T>, phi:Formula)  
	requires wfStructure(B) && wfFormula(B.Sig, phi) && f.Values <= B.Dom
	decreases phi
{
(freeVar(phi) <= f.Keys) &&
match phi
    case Atom(R, par) =>   HOmap(f, par) in B.I[R] 
    case And(phi0, phi1) => models(B, f, phi0) && models(B, f, phi1)
    case Forall(x, alpha) => forall v :: v in B.Dom  ==>  models(B, f[x:=v], alpha)
    case Exists(x, alpha) => exists v :: v in B.Dom  &&  models(B, f[x:=v], alpha) 
}

// Lemmas on the predicate models

lemma safeProjection_Lemma<T>(B:Structure<T>, f:Valuation<T>, U:set<Name>, phi:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, phi) && f.Values <= B.Dom
	requires freeVar(phi) <= U <= f.Keys 
	ensures models(B, f, phi) <==> models(B, projectVal(f,U), phi)
	decreases phi
{
  if phi.Atom? {  
	   HOmapProject_Lemma(f,U,phi.par); 
  } else if phi.Forall? || phi.Exists? { 
			 var (x,alpha) := if phi.Forall? then (phi.x,phi.Body) else (phi.x, phi.Body);
			 forall v | v in B.Dom 
					  {calc{
							models(B,f[x:=v],alpha);
								 { 
								 safeProjection_Lemma(B,f[x:=v],U+{x},alpha); 
								 }
							models(B,projectVal(f[x:=v],U+{x}),alpha);
							     {
								 assert projectVal(f[x:=v],U+{x}) == projectVal(f,U)[x:=v];
								 }
							models(B,projectVal(f,U)[x:=v],alpha);
					  }}
	} else if phi.And? {} // phi.And? is automatically proved
}

lemma freeVarsDep_Lemma<T>(B:Structure<T>, f:Valuation<T>, g:Valuation<T>, phi:Formula)
  requires wfStructure(B) && wfFormula(B.Sig, phi) && f.Values <= B.Dom && g.Values <= B.Dom
  requires freeVar(phi) <= f.Keys && freeVar(phi) <= g.Keys
  requires projectVal(f, freeVar(phi)) ==  projectVal(g, freeVar(phi))
  requires models(B, f, phi) 
  ensures models(B, g, phi)
{  
  safeProjection_Lemma(B, f, freeVar(phi), phi);
	// assert models(B,projectVal(f, freeVar(phi)),phi);
	// assert models(B,projectVal(g, freeVar(phi)),phi);
  safeProjection_Lemma(B, g, freeVar(phi), phi);
}

lemma modelsAnd_Lemma<T> (B:Structure<T>,f:Valuation<T>,phi:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, phi) && f.Values <= B.Dom
	requires phi.And?
	ensures models(B,f,phi) <==>								
	        ( freeVar(phi.0) <= f.Keys && models(B, projectVal(f,freeVar(phi.0)), phi.0) 
	          && freeVar(phi.1) <= f.Keys && models(B, projectVal(f,freeVar(phi.1)), phi.1)  )
{
 if models(B,f,phi) 
  {
  safeProjection_Lemma(B, f, freeVar(phi.0), phi.0);
  safeProjection_Lemma(B, f, freeVar(phi.1), phi.1);
  }
  if freeVar(phi.0) <= f.Keys && models(B, projectVal(f,freeVar(phi.0)), phi.0) 
	 && freeVar(phi.1) <= f.Keys && models(B, projectVal(f,freeVar(phi.1)), phi.1) 
  {
  safeProjection_Lemma(B, f, freeVar(phi.0), phi.0);
  safeProjection_Lemma(B, f, freeVar(phi.1), phi.1);
  }
}

lemma NoFreeVar_Lemma<T>(B:Structure, f:Valuation<T>, x:Name,  a:T, beta:Formula)
	requires wfStructure(B) && wfFormula(B.Sig,beta) && f.Values <= B.Dom
	requires x !in freeVar(beta)
	requires a in B.Dom
	ensures models(B, f[x:=a], beta) <==> models(B, f, beta)
{ 
  if models(B, f[x:=a], beta) { 
	 varNotInProjectVal_Lemma(f, x, a, freeVar(beta)); 
     safeProjection_Lemma(B, f[x:=a], freeVar(beta), beta);
	 safeProjection_Lemma(B, f, freeVar(beta), beta);
     }
  if models(B, f, beta) {
	 varNotInProjectVal_Lemma(f, x, a, freeVar(beta)); 
     safeProjection_Lemma(B, f[x:=a], freeVar(beta), beta);
	 safeProjection_Lemma(B, f, freeVar(beta), beta);
	 }
}

lemma NoFreeVarInForall_Lemma<T>(B:Structure, f:Valuation<T>, x:Name, beta:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, beta) && f.Values <= B.Dom
	requires x !in freeVar(beta)
	ensures models(B, f, beta) <==> models(B, f, Forall(x,beta))
{ 
forall a  | a in B.Dom { NoFreeVar_Lemma(B, f, x, a, beta); }
}


lemma NoFreeVarInExists_Lemma<T>(B:Structure, f:Valuation<T>, x:Name, beta:Formula)
  requires wfStructure(B) && wfFormula(B.Sig,beta) && f.Values <= B.Dom
  requires x !in freeVar(beta)
  ensures models(B,f,beta) <==> models(B,f,Exists(x,beta))
{   
forall a  | a in B.Dom { NoFreeVar_Lemma(B, f, x, a, beta); }			
}

lemma weakExists_Lemma<T>(B:Structure<T>, f:Valuation<T>, x:Name, phi:Formula)
  requires wfStructure(B) && wfFormula(B.Sig, phi) && f.Values <= B.Dom 
  requires models(B, f, phi) 
  ensures models(B, f, Exists(x,phi))
{
if x !in freeVar(phi) { NoFreeVarInExists_Lemma(B, f, x, phi);
} else {
        assert f == f[x:=f[x]];
        assert models(B, f[x:=f[x]], phi);
        var v := f[x];
        assert v in B.Dom && models(B, f[x:=v], phi);
        }
}

lemma  Existsmodels_Lemma<T>(B:Structure<T>, f:Valuation<T>, x:Name, beta:Formula)
    requires wfStructure(B) && wfFormula(B.Sig, Exists(x,beta)) && f.Values <= B.Dom
    requires x in freeVar(beta) && models(B,f,beta)
	ensures models(B, projectVal(f,freeVar(beta)-{x}),Exists(x,beta))
{
var v :| v in B.Dom && f[x] == v;
safeProjection_Lemma(B, f, freeVar(beta), beta);
assert models(B, projectVal(f,freeVar(beta)),beta);
ExtProjectVal_Lemma(B, f, x, freeVar(beta), v);
assert projectVal(f,freeVar(beta)) == projectVal(f,freeVar(beta)-{x})[x:=v];
assert models(B, projectVal(f,freeVar(beta)-{x}),Exists(x,beta));
}

lemma Exists_Commutes_Lemma<T>(x:Name, y:Name, alpha:Formula, f:Valuation<T>, B:Structure<T>)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom
	requires models(B, f, Exists(x, Exists(y, alpha))) 
	ensures models(B, f, Exists(y, Exists(x, alpha)))
{
calc ==> { 
		 models(B, f, Exists(x, Exists(y, alpha)));
		 freeVar(Exists(x, Exists(y, alpha))) <= f.Keys &&
		   exists v, v' :: v in B.Dom && v' in B.Dom && models(B, f[x:=v][y:=v'], alpha);
			  {
			   assert x != y ==> (forall v, v' :: v in B.Dom && v' in B.Dom 
								 ==> f[x:=v][y:=v'] == f[y:=v'][x:=v]);
			   }
		 freeVar(Exists(y, Exists(x, alpha))) <= f.Keys &&
		   exists v', v :: v' in B.Dom && v in B.Dom && models(B, f[y:=v'][x:=v], alpha);
		 models(B, f, Exists(y, Exists(x, alpha)));
		 } 
}

} 