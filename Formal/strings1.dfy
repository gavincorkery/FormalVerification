method isPrefix(pre: string, str: string) returns (res:bool)
{
    if(|pre| > |str|){
        return false;
    }
    return str[..|pre|] == pre;
}

method isSubstring(sub:string, str:string) returns(res:bool)  
{
  var i:= 0;
  while(i<|str|){
    var prefix := isPrefix(sub, str[i..]);
    if(prefix)
    {
      return true;
    }
    i := i + 1;
  }
  return false;
}  

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
{
    if(k==0)
    {
        return true;
    }
    var i := 0;
    while(i < |str1|-k)
    {
        var endIndex := i + k;
        var substringFound := isSubstring(str1[i..endIndex], str2);
        if(substringFound)
        {
            return true;
        } 
    }
    return false;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat) 
{
	var maxLen:= |str1|;
	while(maxLen>0) 
    {
        var commonSubstringFound := haveCommonKSubstring(maxLen, str1, str2);
		if(commonSubstringFound){
			return maxLen;
		}
		maxLen := maxLen - 1;
	}
}
