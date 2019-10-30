include "QCSP-Instance.dfy"

module Conjunctive_Pos_Logic{
  import opened Utils 
  import opened from_QCSP_Instance = QCSP_Instance`Lemmas_for_Conjunctive_Pos_Logic
  export Lemmas_for_PS_Soundness 
         provides Utils, from_QCSP_Instance, 
		          existSq_Forall_Lemma, existSq_ExtVal_Lemma, ExistsProject_Lemma, 
		          existSq_Distr_And_Lemma, existSq_Exists_Commutes_Lemma,
		          existSq_Sum_Lemma, existSqSem_Lemma	
		 reveals existSq

function existentialClosure(alpha:Formula):Formula
	ensures sentence(existentialClosure(alpha))
{
existSq(freeVar(alpha),alpha)
}

function existSq(X:set<Name>, alpha:Formula):Formula
	ensures freeVar(existSq(X,alpha)) == freeVar(alpha)-X
	ensures forall S :: wfFormula(S,alpha) ==> wfFormula(S,existSq(X,alpha)) 
{
if |X| == 0 then alpha else var x :| x in X;
						    Exists(x,existSq(X-{x},alpha))
}

lemma existSq_Exists_Commutes_Lemma<T>(B:Structure<T>, f:Valuation<T>, y: Name, X:set<Name>, alpha:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom
	ensures  models(B, f, existSq(X, Exists(y, alpha))) 
	         <==> models(B, f, Exists(y, existSq(X, alpha)))
	decreases X
{
if |X| > 0
	{
	var x :| x in X && ( existSq(X, Exists(y, alpha)) 
						  == Exists(x, existSq(X-{x}, Exists(y, alpha))) );
	var v :| v in B.Dom && ( models(B, f[x:=v], existSq(X-{x}, Exists(y, alpha)))
							 <==> models(B, f, existSq(X, Exists(y, alpha))) );
	var f' := f[x:=v];
	assert f'.Values <= f.Values + {v} ;
	assert f'.Values <= B.Dom;
	calc {
		 models(B, f, existSq(X, Exists(y, alpha)));
		   { existSq_Exists_Commutes_Lemma(B, f[x:=v], y, X-{x}, alpha); } 
		 models(B, f[x:=v], Exists(y, existSq(X-{x}, alpha)));
		 models(B, f, Exists(x, Exists(y, existSq(X-{x}, alpha))));
		   { 
		   if models(B, f, Exists(x, Exists(y, existSq(X-{x}, alpha))))
			  { Exists_Commutes_Lemma(x, y, existSq(X-{x}, alpha), f, B); }
		   if models(B, f, Exists(y, Exists(x, existSq(X-{x}, alpha))))
			  { Exists_Commutes_Lemma(y, x, existSq(X-{x}, alpha), f, B); }
		   }
		 models(B, f, Exists(y, Exists(x, existSq(X-{x}, alpha))));
		 models(B, f, Exists(y, existSq(X, alpha)));
		 }				
	}
}

lemma existSqPlusVar_Lemma<T>(B:Structure<T>, f:Valuation<T>, y:Name, X:set<Name>, alpha:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom
	requires y !in X 
	ensures models(B, f, existSq(X+{y}, alpha)) 
			<==> models(B, f, Exists(y, existSq(X, alpha)))	
	decreases X 
{
var Y := X + {y};
var x :| x in Y && existSq(Y, alpha) == Exists(x, existSq(Y-{x}, alpha));
if x != y { 
	var Z := X-{x};								
	calc {
	     models(B, f, existSq(Y, alpha));
		 models(B, f, Exists(x, existSq(Y-{x}, alpha)));
		   { assert Y - {x} == Z + {y}; }
		 models(B, f, Exists(x, existSq(Z + {y}, alpha)));
		 exists v :: v in B.Dom && models(B, f[x:=v], existSq(Z+{y}, alpha));
		   { forall v | v in B.Dom { existSqPlusVar_Lemma(B, f[x:=v],y, Z, alpha); } } 
		 exists v :: v in B.Dom && models(B, f[x:=v], Exists(y, existSq(Z, alpha)));
		 models(B, f, Exists(x, Exists(y, existSq(Z, alpha))));
		   { 
		   if models(B, f, Exists(x, Exists(y, existSq(Z, alpha))))
		      { Exists_Commutes_Lemma(x, y, existSq(Z,alpha), f, B); }
		   if models(B, f, Exists(y, Exists(x, existSq(Z, alpha))))
		      { Exists_Commutes_Lemma(y, x, existSq(Z,alpha), f, B); }
		   }
		 models(B, f, Exists(y, Exists(x, existSq(Z, alpha))));
		 exists v :: v in B.Dom && models(B, f[y:=v], Exists(x, existSq(Z, alpha)));
		   { forall v | v in B.Dom { existSqPlusVar_Lemma(B, f[y:=v], x, Z, alpha); }}
		 exists v :: v in B.Dom && models(B, f[y:=v], existSq(Z+{x}, alpha));
		   { assert Z+{x} == X; }
		 models(B, f, Exists(y, existSq(X, alpha)));
		 }
	}
}

lemma existSq_Lemma<T>(B:Structure<T>, f:Valuation<T>, x:Name, X:set<Name>, alpha:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom
	requires x in X 
	ensures models(B, f, Exists(x, existSq(X-{x}, alpha))) 
	        <==> models(B, f, existSq(X, alpha))
{
existSqPlusVar_Lemma(B, f, x, X-{x}, alpha);
assert X == (X-{x})+{x};
}

lemma existSq_ExtVal_Lemma<T>(B:Structure<T>, f:Valuation<T>, W:seq<Name>, V:seq<T>, X:set<Name>, alpha:Formula)
	  requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom 
	  requires noDups(W) && |W| == |V| == |X| && setOf(V) <= B.Dom && X == setOf(W) 
	  requires extVal(f,W,V).Values <= B.Dom && models(B, extVal(f,W,V), alpha)
	  ensures wfFormula(B.Sig, existSq(X, alpha))
	  ensures models(B, f, existSq(X, alpha)) 
	  decreases X
{
if |X| > 0 {
	 var z :| z in X && existSq(X, alpha) == Exists(z, existSq(X-{z}, alpha));
	 var i :| 0 <= i < |W| && W[i] == z;
	 var W' := W[..i] + W[i+1..];
	 var V' := V[..i] + V[i+1..];
	 var X1 := setOf(W[..i]);
	 var X2 := setOf(W[i+1..]);
	 // assert X1 + X2 == X - {z} ;
	 extValOrder_Lemma(i,W,V,f);
	 assert noDups(W');
	 assert extVal(f[z:=V[i]], W', V') == extVal(f, W, V);	
	 assert models(B,extVal(f[z:=V[i]],W',V'),alpha);
	 assert X-{z} == setOf(W');
	 existSq_ExtVal_Lemma(B, f[z:=V[i]], W', V', X-{z}, alpha); 
	 assert models(B,f[z:=V[i]],existSq(X-{z},alpha));
	 if X == {z}  { 
	    assert existSq(X-{z},alpha) == alpha;
		//assert wfModel(B,f[z:=V[i]],alpha);
		assert models(B,f[z:=V[i]],alpha);
		assert V[i] in B.Dom;
		assert exists v:: v == V[i] && v in B.Dom && models(B,f[z:=v],alpha);
		assert f[z:=V[i]].Values <= f.Values + {V[i]} <= B.Dom;
	    assert models(B,f,existSq({z},alpha)); 
	 } else { 
	    assert f[z:=V[i]] == extVal(f,[z],[V[i]]);
		existSq_ExtVal_Lemma(B, f, [z],[V[i]],{z},existSq(X-{z},alpha));
		// assert models(B,f,Exists(z,existSq(X-{z},alpha)));
	    existSq_Lemma(B, f, z, X, alpha);
		// assert models(B,f,existSq(X,alpha));
	  }
}
}

lemma ExistsProject_Lemma<T>(B:Structure<T>, f:Valuation<T>, U:set<Name>, alpha:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom
	requires U <= f.Keys 
	requires wfFormula(B.Sig,existSq(freeVar(alpha)-f.Keys, alpha))
	requires models(B,f,existSq(freeVar(alpha)-f.Keys, alpha))
	ensures wfFormula(B.Sig,existSq(freeVar(alpha)-U,alpha))
	ensures models(B,projectVal(f,U),existSq(freeVar(alpha)-U,alpha))
	decreases f.Keys-U
{
if f.Keys == U {
		assert projectVal(f,f.Keys) == f;
} else	{
		var x:| x in f.Keys && x !in U;
		ExistsProject_Lemma(B, f, U+{x}, alpha);
		assert models(B,projectVal(f,U+{x}),existSq(freeVar(alpha)-(U+{x}),alpha));
		assert projectVal(f,U+{x}) == projectVal(f,U)[x:=f[x]];
        assert models(B, projectVal(f,U)[x:=f[x]],existSq(freeVar(alpha)-(U+{x}),alpha));
		assert f[x] in B.Dom;
		assert models(B, projectVal(f,U),Exists(x, existSq(freeVar(alpha)-(U+{x}),alpha)));
		assert freeVar(alpha)-(U+{x}) == (freeVar(alpha)-U)-{x};
		assert models(B, projectVal(f,U),Exists(x, existSq((freeVar(alpha)-U)-{x},alpha)));
        if x in freeVar(alpha) {
				existSq_Lemma(B, projectVal(f,U), x, freeVar(alpha)-U, alpha);
		} else	{ // x !in freeVar(alpha)
				assert 	(freeVar(alpha)-U)-{x} == freeVar(alpha)-U;
				assert models(B, projectVal(f,U),Exists(x, existSq((freeVar(alpha)-U),alpha)));
				NoFreeVarInExists_Lemma(B, projectVal(f,U), x, existSq((freeVar(alpha)-U),alpha));
				}
		}
}

lemma existSq_Distr_And_Lemma<T>(B:Structure<T>, f:Valuation<T>, W:set<Name>, phi:Formula)
	requires wfStructure(B) && wfFormula(B.Sig,phi) && f.Values <= B.Dom 
	requires phi.And?
	requires models(B,f, existSq(W,phi))  
	ensures wfFormula(B.Sig,existSq(W*freeVar(phi.0),phi.0))
	ensures wfFormula(B.Sig,existSq(W*freeVar(phi.1),phi.1))
	ensures models(B, f, existSq(W*freeVar(phi.0), phi.0))
	ensures models(B, f, existSq(W*freeVar(phi.1), phi.1)) 
	decreases W
{
if W != {}
    {
    var x:| x in W ;
    existSq_Lemma(B, f, x, W, phi);
    var a:| a in B.Dom && models(B,f[x:=a],existSq(W-{x},phi));
	assert f[x:=a].Values <= B.Dom;
    existSq_Distr_And_Lemma(B,f[x:=a],W-{x},phi);
    //assert models(B, f[x:=a], existSq((W-{x})*freeVar(phi.0), phi.0));
    //assert models(B, f[x:=a], existSq((W-{x})*freeVar(phi.1), phi.1));
    //assert (W-{x})*freeVar(phi.0) <= freeVar(phi.0);
    //assert (W-{x})*freeVar(phi.1) <= freeVar(phi.1);
    assert models(B, f, Exists(x, existSq((W-{x})*freeVar(phi.0), phi.0)));
    assert models(B, f, Exists(x,existSq((W-{x})*freeVar(phi.1), phi.1)));
    if x !in freeVar(phi.0) {
        NoFreeVarInExists_Lemma(B,f, x, existSq((W-{x})*freeVar(phi.0), phi.0));
        assert W*freeVar(phi.0) == (W-{x})*freeVar(phi.0);
        assert models(B, f, existSq(W*freeVar(phi.0), phi.0));
    } else {
        assert (W-{x})*freeVar(phi.0) == W*freeVar(phi.0)-{x};
        assert  models(B, f, Exists(x,existSq((W*freeVar(phi.0))-{x}, phi.0)));
        existSq_Lemma(B, f, x, W*freeVar(phi.0), phi.0);
        assert models(B, f, existSq(W*freeVar(phi.0), phi.0));
    }
    if x !in freeVar(phi.1) {
        NoFreeVarInExists_Lemma(B,f, x, existSq((W-{x})*freeVar(phi.1), phi.1));
        assert W*freeVar(phi.1) == (W-{x})*freeVar(phi.1);
        assert models(B, f, existSq(W*freeVar(phi.1), phi.1));
    } else {
        assert (W-{x})*freeVar(phi.1) == W*freeVar(phi.1)-{x};
        assert  models(B, f, Exists(x,existSq((W*freeVar(phi.1))-{x}, phi.1)));
        existSq_Lemma(B, f, x, W*freeVar(phi.1), phi.1);
        assert models(B, f, existSq(W*freeVar(phi.1), phi.1));
    }
    }
}

lemma existSqSem_Lemma<T>(B:Structure<T>, f:Valuation<T>, X:set<Name>, alpha:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom
	requires wfFormula(B.Sig, existSq(X, alpha)) && X !! f.Keys
	requires models(B, f, existSq(X, alpha)) 
	ensures exists W,V :: setOf(V) <= B.Dom   && |W| == |V| == |X| && setOf(W) == X 
	                     && noDups(W) && setOf(W) !! f.Keys
						 && extVal(f,W,V).Values <= B.Dom
						 && models(B, extVal(f,W,V), alpha)
	decreases X
{
if |X| > 0 
    {
     var z :| z in X && existSq(X, alpha) 
	                    == Exists(z, existSq(X-{z}, alpha));	
	 var v :| v in B.Dom && models(B, f[z:=v], existSq(X-{z}, alpha));
	 existSqSem_Lemma(B, f[z:=v], X-{z}, alpha);	
	 var W',V' :|  setOf(V') <= B.Dom 
	               && |W'|==|V'| == |X-{z}| 
	               && setOf(W') == X-{z} 
				   && noDups(W') && setOf(W') !! f[z:=v].Keys
				   && extVal(f[z:=v],W',V').Values <= B.Dom
				   && models(B, extVal(f[z:=v], W', V'), alpha);
	 var W, V := [z] + W', [v] + V';	
	 assert setOf(V) <= B.Dom;
	 assert |W| == |V| == |X|; 
	 assert setOf(W) == setOf(W')+{z} == (X-{z})+{z} == X; 
	 assert noDups(W);
	 assert z !in f.Keys;
	 assert setOf(W) !! f.Keys;
	 extValDomRange_Lemma(f, W, V);
	 assert extVal(f,W,V).Values <= B.Dom;
	 assert extVal(f[z:=v], W', V') == extVal(f,W,V);
	 assert models(B, extVal(f,W,V), alpha);
	} 
}

lemma WeakerexistSq_Lemma<T>(B:Structure<T>, h:Valuation<T>, W:set<Name>, 
                                 phi:Formula, psi:Formula)
	requires wfStructure(B) && wfFormula(B.Sig,phi) && wfFormula(B.Sig,psi) && h.Values <= B.Dom
	requires forall f:Valuation<T> :: f.Values <= B.Dom && models(B,f,phi) ==> models(B,f,psi)
	requires models(B,h,existSq(W,phi)) && W !! h.Keys
	ensures  wfFormula(B.Sig,existSq(W,psi))
	ensures  models(B,h,existSq(W,psi))
{
existSqSem_Lemma(B, h, W, phi);
var W',V :| setOf(V) <= B.Dom 
                && |W'| == |V| == |W|  
                && setOf(W') == W
				&& noDups(W') 
				&& extVal(h,W',V).Values <= B.Dom
				&& models(B,extVal(h,W',V),phi);
existSq_ExtVal_Lemma(B, h, W', V, W, psi);
}

lemma existSq_Forall_Lemma<T>(B:Structure<T>, h:Valuation<T>, x:Name, W:set<Name>, phi:Formula)
	requires wfStructure(B) && wfFormula(B.Sig,Forall(x,phi)) && h.Values <= B.Dom 
	requires models(B,h,existSq(W,Forall(x,phi))) && W !! h.Keys
	ensures  wfFormula(B.Sig,existSq(W,Exists(x,phi)))
	ensures  models(B,h,existSq(W,Exists(x,phi)))		
{
WeakerexistSq_Lemma(B, h, W, Forall(x,phi), Exists(x,phi));
}

lemma existSqCommutes_Lemma<T>(B:Structure<T>, f:Valuation<T>, X:set<Name>, Y:set<Name>, alpha:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom 
	requires models(B, f, existSq(X, existSq(Y, alpha))) && (X+Y) !! f.Keys  && X!!Y
	ensures wfFormula(B.Sig, existSq(Y, existSq(X, alpha))) 
	ensures models(B, f, existSq(Y, existSq(X, alpha))) 
	decreases X
{
if X != {} 
    {
    var x :| x in X;
	assert x !in f.Keys;
	if X == {x} { existSq_Exists_Commutes_Lemma(B,f,x,Y,alpha);
	} else {
			assert models(B, f, existSq(X, existSq(Y, alpha)));
			existSq_Lemma(B, f, x, X, existSq(Y, alpha));
			assert models(B, f, Exists(x,existSq(X-{x}, existSq(Y, alpha))));
			var v :| v in B.Dom && models(B, f[x:=v], existSq(X-{x}, existSq(Y, alpha)));
			assert ((X-{x})+Y) < X+Y;
			assert ((X-{x})+Y) !! f[x:=v].Keys;
			existSqCommutes_Lemma (B, f[x:=v], X-{x}, Y, alpha);
			assert models(B, f[x:=v], existSq(Y, existSq(X-{x}, alpha)));
			assert models(B, f, existSq({x},existSq(Y, existSq(X-{x}, alpha))));
			existSqCommutes_Lemma (B, f, {x}, Y, existSq(X-{x}, alpha));
			assert models(B, f, existSq(Y,Exists(x, existSq(X-{x}, alpha))));
			existSqSem_Lemma(B, f, Y, Exists(x, existSq(X-{x}, alpha)));
			var W,V :| setOf(V) <= B.Dom && |W| == |V| == |Y|  && setOf(W) == Y && noDups(W) 
			       && setOf(W) !! f.Keys
				   && extVal(f,W,V).Values <= B.Dom
				   && models(B, extVal(f,W,V), Exists(x, existSq(X-{x}, alpha)));
			existSq_Lemma(B, extVal(f,W,V), x, X, alpha);
			assert models(B, extVal(f,W,V), existSq(X, alpha));
			existSq_ExtVal_Lemma(B, f, W, V, Y, existSq(X, alpha));
			assert models(B, f, existSq(Y, existSq(X, alpha)));
		    }
    }
}
   
lemma existSq_Sum_Intro_Lemma<T>(B:Structure<T>, f:Valuation<T>, X:set<Name>, Y:set<Name>, alpha:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom
	requires X !! Y 
	requires wfFormula(B.Sig, existSq(X, existSq(Y, alpha))) 
	requires models(B, f, existSq(X, existSq(Y, alpha))) 
	ensures wfFormula(B.Sig, existSq(X+Y, alpha))
	ensures models(B, f, existSq(X+Y, alpha))
	decreases X
{
if |X| > 0 {
	var x :| x in X && existSq(X, existSq(Y, alpha)) 
			           == Exists(x, existSq(X-{x}, existSq(Y, alpha)));
	assert models(B, f, Exists(x, existSq(X-{x}, existSq(Y, alpha))));
    var v:| v in B.Dom 
		    && models(B, f[x:=v], existSq(X-{x}, existSq(Y, alpha)));
	existSq_Sum_Intro_Lemma(B, f[x:=v], X-{x}, Y, alpha);
	assert models(B, f[x:=v], existSq((X-{x})+Y, alpha));
	assert (X-{x})+Y == (X+Y)-{x};
	assert models(B, f, Exists(x, existSq((X+Y)-{x}, alpha)));
	existSq_Lemma(B, f, x, X+Y, alpha);
	assert models(B, f, existSq(X+Y, alpha));
	}
}

lemma existSq_Sum_Unfold_Lemma<T>(B:Structure<T>, f:Valuation<T>, X:set<Name>, Y:set<Name>, alpha:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom
	requires X !! Y  && (X+Y) !! f.Keys
	requires wfFormula(B.Sig, existSq(X+Y, alpha))
	requires models(B, f, existSq(X+Y, alpha))
	ensures wfFormula(B.Sig, existSq(X, existSq(Y, alpha))) 
	ensures models(B, f, existSq(X, existSq(Y, alpha))) 
	decreases X+Y
{
if |X+Y| > 0 {
    var z :| z in X+Y && existSq(X+Y, alpha)
			           == Exists(z, existSq((X+Y)-{z}, alpha));
	assert models(B, f, Exists(z, existSq((X+Y)-{z}, alpha)));
	var v:| v in B.Dom && models(B, f[z:=v], existSq((X+Y)-{z}, alpha));
	if z in X {
	   assert (X+Y)-{z} == (X-{z})+Y;
	   assert models(B, f[z:=v], existSq((X-{z})+Y, alpha));
	   existSq_Sum_Unfold_Lemma(B, f[z:=v], X-{z}, Y, alpha);
	   assert models(B, f[z:=v], existSq(X-{z}, existSq(Y, alpha)));
	   assert models(B, f, Exists(z, existSq(X-{z}, existSq(Y, alpha))));
	   existSq_Lemma(B, f, z, X, existSq(Y, alpha)); 
	   assert models(B, f, existSq(X, existSq(Y, alpha)));
	} else { 
	   assert z in Y && (X+Y)-{z} == (Y-{z})+X;
	   assert models(B, f[z:=v], existSq((Y-{z})+X, alpha));
	   existSq_Sum_Unfold_Lemma(B, f[z:=v], Y-{z}, X, alpha);
	   assert models(B, f[z:=v], existSq(Y-{z}, existSq(X, alpha)));
	   assert models(B, f, Exists(z, existSq(Y-{z}, existSq(X, alpha))));
	   existSq_Lemma(B, f, z, Y, existSq(X, alpha)); 
	   assert models(B, f, existSq(Y, existSq(X, alpha)));
	   existSqCommutes_Lemma(B, f, Y, X, alpha);
	   assert models(B, f, existSq(X, existSq(Y, alpha)));
	   }
	   }
}

lemma existSq_Sum_Lemma<T>(B:Structure<T>, f:Valuation<T>, X:set<Name>, Y:set<Name>, alpha:Formula)
	requires wfStructure(B) && wfFormula(B.Sig, alpha) && f.Values <= B.Dom
	requires X !! Y  && (X+Y) !! f.Keys
	ensures wfFormula(B.Sig, existSq(X, existSq(Y, alpha))) 
	        && wfFormula(B.Sig, existSq(X+Y, alpha))
	ensures models(B, f, existSq(X, existSq(Y, alpha))) 
	        <==> models(B, f, existSq(X+Y, alpha))
	decreases X
{
if models(B, f, existSq(X, existSq(Y, alpha))) 
     { existSq_Sum_Intro_Lemma(B, f, X, Y, alpha); }
if models(B, f, existSq(X+Y, alpha))
     { existSq_Sum_Unfold_Lemma(B, f, X, Y, alpha); }
}

}