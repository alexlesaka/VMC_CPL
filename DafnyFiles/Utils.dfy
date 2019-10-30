module Utils {
  export reveals setOf, noDups, allMaps, choose
         provides allMaps_Correct_Lemma, ExtMap_Lemma, ProyectMap_Lemma

function method setOf<T>(s:seq<T>): set<T> 
{
set x | x in s
}

predicate noDups<T>(U:seq<T>)
{
forall i,j :: 0 <= i < j < |U| ==> U[i] != U[j]
}

function allMaps<A,B>(keys: set<A>, values: set<B>): set<map<A,B>>
    ensures forall m :: m in allMaps(keys, values) ==> m.Keys == keys && m.Values <= values
{
if keys == {} then {map[]}
else 
    var k := choose(keys);
    var M := allMaps(keys - {k}, values);
    set m,v | m in M && v in values :: m[k := v]
}

function choose<A>(s: set<A>): A
    requires s != {}
{
// By putting this expression in a function, we can use this same
// function in both allMaps and allMaps_Correct.  (If we used this
// Hilbert epsilon operator directly in the two places, each place
// may choose a different element, which makes the proof much harder.)
var a :| a in s; a
}

// Here is a proof that allMaps does indeed return a set of all maps
lemma allMaps_Correct_Lemma<A,B>(p: map<A,B>, values: set<B>)
    requires p.Values <= values
    ensures p in allMaps(p.Keys, values)
{
if p.Keys == {} {
    assert p == map[];
} else {
    var k := choose(p.Keys);
    var M := allMaps(p.Keys - {k}, values);
    var S := set m,v | m in M && v in values :: m[k := v];
    assert S == allMaps(p.Keys, values);

    var p' := map k' | k' in p.Keys && k' != k :: p[k'];
    assert p'.Keys == p.Keys - {k};
    assert p'.Values <= values;
    assert p == p'[k := p[k]];

    var S' := allMaps(p'.Keys, values);
    allMaps_Correct_Lemma(p', values);

    assert p' in M && p[k] in values;
    assert exists m,v :: m in M && v in values && p == m[k := v];
    assert p in S;
}
}

lemma ExtMap_Lemma<A,B>(p: map<A,B>, x:A, v:B, keys:set<A>, values:set<B>)
	requires p in allMaps(keys-{x},values)
	requires x in keys && v in values
	ensures p[x:=v] in allMaps(keys,values)
{
assert p[x:=v].Keys == p.Keys + {x} == keys-{x}+{x} == keys;
allMaps_Correct_Lemma(p[x:=v],values);
}

lemma ProyectMap_Lemma<A,B>(p: map<A,B>, subkeys:set<A>, keys:set<A>, values:set<B>)
	requires p in allMaps(keys,values)
	requires subkeys <= keys
	ensures (map s | s in subkeys :: p[s]) in allMaps(subkeys,values)
{
var p' := (map s | s in subkeys :: p[s]);
assert (map s | s in subkeys :: p[s]).Keys == subkeys;
allMaps_Correct_Lemma(p',values);
}

} 