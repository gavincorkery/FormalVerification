// CS4004 Project Part 2: Specification
// Due: 03/11/2017
// Authors: Gavin Corkery, Sean Durban

predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	|pre| > |str| || pre != str[..|pre|]
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

predicate isSubstringPred(sub:string, str:string)
{
  //TODO
}

predicate isNotSubstringPred(sub:string, str:string)
{
	//TODO: your FOL formula should start with a forall
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
  (k <= |str1| && k <= |str2|) && (exists x :: (isSubstringPred(x, str1) && isSubstringPred(x, str2)) && |x| == k)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	(k > |str1| || k > |str2|) || forall x :: !((isSubstringPred(x, str1) && isSubstringPred(x, str2)) && |x| == k)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}

