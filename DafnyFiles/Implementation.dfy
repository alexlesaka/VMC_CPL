include "PS-Completeness.dfy"

module Implementation {
	import opened Utils
	import opened QCSP_Instance`Lemmas_for_PS_Completeness
	import opened Proof_System`Lemma_and_Defs 
	import opened PS_Completeness`function_methods_for_Implementation 

/* CODE GENERATION FOR function canonical_judgement 
   BY IMPLEMENTATION OF method compute_canonical_judgement 
   AND ITS AUXILIARIES. 
   CONTRACT ENSURES THAT method compute_canonical_judgement 
   INDEED COMPUTES function canonical_judgement  */

method compute_AllMaps<T(==)> (keys:seq<Name>, values:set<T>) returns (am:set<map<Name,T>>)
	requires values != {} && noDups(keys) 
	ensures am == allMaps(setOf(keys), values);  
{
if keys == [] {
     am :=  {map[]};
	 //trivial since allMaps is revealed in Utils's export list
} else { 
    var am' := compute_AllMaps(keys[1..], values);
	am := (set f,v | f in am' && v in values :: f[keys[0]:=v]);
	//Proof of the postcondition
	forall h | h in am 
	  ensures h in allMaps(setOf(keys), values)
		{
		assert exists f,v :: f in allMaps(setOf(keys[1..]), values) 
		                     && v in values && h == f[keys[0]:=v];
		assert h.Keys == setOf(keys) && h.Values <= values;
		allMaps_Correct_Lemma(h,values);
		assert h in allMaps(setOf(keys), values);
		}
    assert am <= allMaps(setOf(keys), values);
	forall h | h in allMaps(setOf(keys), values) 
		ensures h in am
		{
		assert am' == allMaps(setOf(keys[1..]), values); 
		var f := (map k' | k' in h.Keys && k' != keys[0] :: h[k']) ;
		assert f.Keys == setOf(keys)-{keys[0]} == setOf(keys[1..]);
		allMaps_Correct_Lemma(f, values);
		assert f in allMaps(setOf(keys[1..]), values); 
		assert f in am';
		var v := h[keys[0]];
		assert v in values;
		assert h == f[keys[0]:=v];
		assert h in am;
		}
	assert am == allMaps(setOf(keys), values);
	}
}

predicate method leq(n1:Name, n2:Name)
{
n1 == [] || (n2 != [] && ( n1[0] < n2[0] || ( n1[0] == n2[0] && leq(n1[1..],n2[1..]) )))
}

lemma not_leq_Lemma(x:Name, y:Name)
	requires !leq(x,y)
	ensures x != y
{}

lemma leq_trans_Lemma(x:Name, y:Name, z:Name)
	requires leq(x,y) && !leq(z,y)
	ensures leq(x,z)
{}

lemma HasMinimum_Lemma(s: set<Name>)
  requires s != {}
  ensures exists z :: z in s && forall y :: y in s ==> leq(z,y)
{
  var z :| z in s;
  if s == {z} {
    // the mimimum of a singleton set is its only element
	forall y | y in s
		ensures leq(z,y);
	{ if !leq(z,y) { not_leq_Lemma(z, y);} }
  } else if forall y :: y in s ==> leq(z,y) {
    // we happened to pick the minimum of s
  } else {
    // s-{z} is a smaller, nonempty set and it has a minimum
	assert exists k :: k in s && !leq(z,k);
    var s' := s - {z};
    HasMinimum_Lemma(s');
    var z' :| z' in s' && forall y :: y in s' ==> leq(z',y);
    // the minimum of s' is the same as the miminum of s
    forall y | y in s
      ensures leq(z',y)
    {
      if
      case y in s' =>
        // assert leq(z',y);  // because z' in minimum in s'
      case y == z =>
        var k :| k in s && !leq(z, k);  // because z is not minimum in s
		not_leq_Lemma(z, k);
		// assert k != z;
        assert k in s';  // because k != z
		// assert leq(z',k);
		// assert !leq(y,k);
		leq_trans_Lemma(z', k, z);
		// assert leq(z',y);
    }
  }
}

method set2seq(s:set<Name>) returns (seqElem:seq<Name>)
       ensures forall z :: z !in s ==> z !in seqElem
	   ensures noDups(seqElem)
	   ensures setOf(seqElem) == s
{
if s == {} { 
       seqElem := [];
} else {
       HasMinimum_Lemma(s);
       var x :| x in s && forall y :: y in s ==> leq(x, y);
	   var r := set2seq(s-{x});
	   //assert x !in r; // thanks to the first post
	   seqElem := [x] + r;
	   assert setOf(seqElem) == {x} + (s-{x});
       }
}

method compute_join<T>(j1:Judgement<T>, j2:Judgement<T>, phi:Formula, B:Structure<T>) 
       returns (j: Judgement<T>)
	requires wfJudgement(j1,phi,B) && wfJudgement(j2,phi,B)
	requires j1.i == j2.i
	ensures wfJudgement(j,phi,B)  
	ensures j == join(j1,j2,phi,B)
{
var Vars := set2seq(j1.V+j2.V);
//assert B.Dom != {};					//Warning cambio en wfJudgement
var M := compute_AllMaps(Vars, B.Dom);
// assert M == allMaps(j1.V+j2.V, B.Dom);
var F := (set f:Valuation<T> | f in M && projectVal(f,j1.V) in j1.F && projectVal(f,j2.V) in j2.F);
ghost var F' := (set f:Valuation<T> | f in allMaps(j1.V+j2.V, B.Dom)  && projectVal(f,j1.V) in j1.F 
										 && projectVal(f,j2.V) in j2.F);
assert F == F';
j := J(j1.i, j1.V+j2.V, F);
}

method compute_dualProjection<T>(v:Name, j:Judgement<T>, phi:Formula, B:Structure<T>)
       returns (dp: Judgement<T>)
	requires wfJudgement(j,phi,B)
	requires |j.i| > 0 && j.i[..|j.i|-1] + [0] ==j.i 
	requires j.i[..|j.i|-1] in setOfIndex(phi)
	requires FoI(j.i[..|j.i|-1], phi, B.Sig).Forall? && FoI(j.i[..|j.i|-1], phi, B.Sig).x == v
	requires v in j.V 
	ensures wfJudgement(dp, phi, B)
	ensures dp == dualProjection(v,j,phi,B) 
{
indexSubformula_Lemma(j.i[..|j.i|-1],phi, B.Sig);
var Vars := set2seq(j.V-{v});
assert B.Dom != {};						
var M := compute_AllMaps(Vars, B.Dom);
// assert M == allMaps(j1.V+j2.V, B.Dom);
var F := (set f:Valuation<T> | f in M && forall b :: b in B.Dom ==> f[v:=b] in j.F);
ghost var F' := (set f:Valuation<T> | f in allMaps(j.V-{v},B.Dom) 
                                      && forall b :: b in B.Dom ==> f[v:=b] in j.F);
assert F == F';
dp := J(j.i[..|j.i|-1], j.V-{v},  F);
}

function method removeDups<T(==)>(xs:seq<T>):seq<T>
{
if xs == [] then []
else if xs[0] in xs[1..] then removeDups(xs[1..]) 
                         else [xs[0]] + removeDups(xs[1..]) 
}

lemma removeDups_Lemma<T(==)>(xs:seq<T>)
     ensures setOf(removeDups(xs)) == setOf(xs)
     ensures noDups(removeDups(xs))
{
if xs != []  { if xs[0] in xs[1..] { removeDups_Lemma(xs[1..]); }
                              else { 
							         removeDups_Lemma(xs[1..]); 
									 assert setOf(removeDups(xs)) 
									        == {xs[0]} + setOf(removeDups(xs[1..]))
											== setOf(xs);
									 }
             }
}

method compute_canonical_judgement<T>(i:seq<int>, phi:Formula, B:Structure<T>) returns (cj:Judgement<T>)
	requires wfQCSP_Instance(phi,B)
	requires i in setOfIndex(phi)
	ensures wfJudgement(cj,phi,B)  
	ensures cj == canonical_judgement(i,phi,B)
	decreases FoI(i,phi,B.Sig)
{
var phii := FoI(i,phi,B.Sig); 
match phii {
	case Atom(R,par) => {
	                    var ndpar := removeDups(par);
						removeDups_Lemma(par);
	                    var M := compute_AllMaps(ndpar, B.Dom);
						assert allMaps(setOf(ndpar), B.Dom) == allMaps(setOf(par), B.Dom);
	                    var F := (set f:Valuation<T> | f in M && HOmap(f,par) in B.I[R]);
						ghost var F' := (set f:Valuation<T> | f in allMaps(setOf(par),B.Dom)	
								                        &&  HOmap(f,par) in B.I[R]);
						ghost var cj' := J(i, setOf(par), F');
						assert F == F' == canonical_judgement(i,phi,B).F; 
						assert J(i, setOf(par), F) == cj';
						var seqpar := setOf(par);
						cj := J(i, seqpar, F);
						}
	case And(phi0,phi1) =>	{
	                        indexSubformula_Lemma(i,phi,B.Sig);
							var j0': Judgement;
	                        j0':= compute_canonical_judgement(i+[0], phi, B);
							var j1': Judgement;
							j1' := compute_canonical_judgement(i+[1], phi, B);
		 					var j0 := J(i, j0'.V, j0'.F);
							var j1 := J(i, j1'.V, j1'.F);
							cj := compute_join(j0, j1, phi, B);
							}
	case Forall(x,phik) =>  {
	                        indexSubformula_Lemma(i,phi,B.Sig);
	                        var j0 :=compute_canonical_judgement(i+[0],phi,B);								   
							if x in j0.V { cj := compute_dualProjection(x,j0,phi,B); }
							        else { cj := J(i,j0.V,j0.F); }
							}
	case Exists(x,phik) => {
	                       indexSubformula_Lemma(i,phi,B.Sig);
	                       var j0:= compute_canonical_judgement (i+[0],phi,B);
						   var jp := projection(j0,j0.V-{x},phi,B);
						   if x in j0.V { cj := J(i, jp.V, jp.F); } 
						           else { cj := J(i,j0.V,j0.F); }
						   }
          }
}

}