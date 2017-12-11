predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	if (|pre| > |str|) { return false; }

	var i := 0;
	res := true;
	while (i < |pre| && res)
	  invariant 0 <= i <= |pre| <= |str|
	  invariant res ==> pre[..i] == str[..i]
	  invariant !res ==> pre != str[..|pre|]
	  decreases |pre| - i - (if res then 0 else 1);
	{
		if (pre[i] != str[i]) { res := false; }
		else {
		 i := i + 1; 
		}
	}
}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	//ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	if (|sub| > |str|) { return false; }
	var i := 0;
	res := false;
	while (i <= |str|-|sub| && !res) 
	  decreases |str|-|sub| - i - (if res then 1 else 0);
	  invariant 0 <= i <= |str| - |sub| + 1
	  invariant res ==> exists j :: 0 <= j <= |str| &&  isPrefixPred(sub, str[j..])
	  invariant !res ==> forall j :: 0 <= j < i ==> isNotPrefixPred(sub, str[j..])
  {
		res := isPrefix(sub, str[i..]);
		if (!res) {	i := i + 1;	}
	}
}

predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	if |str1| < k || |str2| < k { return false; } 
	if k == 0
	{
		assert isPrefixPred(str1[0..0],str2[0..]);
		return true; 
	} 
	found := false;
	var i := 0;
	while (i <= |str1| - k && !found)
	  invariant 0 <= i <= |str1| - k + 1
	  invariant found ==> haveCommonKSubstringPred(k, str1, str2)
	  invariant !found ==> forall i1, j1 :: 0 <= i1 < i && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
	  decreases |str1| - k - i - (if found then 1 else 0)
	{
		found := isSubstring(str1[i..i+k], str2);
		if (!found) { i := i+1; }
	}
}


method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
	len := |str1|;
	var found : bool := false;
	while (0 < len && !found)
	  invariant 0 <= len <= |str1|
	  invariant found ==> haveCommonKSubstringPred(len,str1,str2)
	  invariant forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k, str1, str2)
	  decreases len - (if found then 1 else 0)
	{
		found := haveCommonKSubstring(len, str1, str2);
		if !found {	len := len - 1; }
	}
  // when len becomes zero the postconditions are still true because of the property written in the following assertion.
	assert isPrefixPred(str1[0..0],str2[0..]);
	return len;
}



