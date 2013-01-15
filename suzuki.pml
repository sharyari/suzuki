#define N 3
#define _empty(_ch) (len(_ch) == 0)
#define _nempty(_ch) (len(_ch) != 0)

typedef Arraychan {
  chan ch = [N] of {short};
}

typedef ArrayArray{
  short ind[N];
}

// This is incremented when entering critical section, and decremented when exiting. Debugging purposes
byte critical;

ArrayArray RN[N]; // "local" copies of RN and LN, have to be visible for both P1 and P2
ArrayArray LN[N]
bool havePrivilege[N]; // True when ones own is set to true. Only someone with privilege alters this
short r,s;  // For looping and such
bool requesting[N]; //True when a process is requesting
Arraychan Q[N]; // Everyone has a local queue
chan gQ = [N] of {short}; // This global channel is for sending privileges 

Arraychan inReq[N]; // These two come in pairs. A REQUEST is sent by adding the index here 
Arraychan inNum[N]; // and adding the REQUEST-ID here

short privLN[N]; // Second parameter in a privilege message

proctype P1(short i){
  short c=0;
  short length=0;
  do
    :: 1 ->
       requesting[i] = true;
       if
	 :: !(havePrivilege[i]) ->
	    atomic {
	      RN[i].ind[i]++;
	      do
		:: c < N && c != i ->
		   inReq[c].ch!i;
		   inNum[c].ch!(RN[i].ind[i]);
		   c++;
		:: c == i ->
		   c++;
		:: else ->
		   break;
	      od;
	    }
	    if
	      :: havePrivilege[i] ->
		 atomic {
		   length = len (gQ);
		   do
		     :: length > 0 ->
			gQ?c;
			Q[i].ch!c;
			length--;
		     :: else ->
			break;
		   od;
		 }
		 c=0;
		 d_step{
		   do
		     :: c < N ->
			LN[i].ind[c] = privLN[c];
			c++;
		     :: else ->
			break;
		   od; 
		 }
	    fi;
	 :: (havePrivilege[i]) ->
	    skip;
       fi;
crit:
       critical++;
       critical--;
exit:  
       d_step{
	 LN[i].ind[i] = RN[i].ind[i];
	 c = 0;
       }
       do
	 :: c == i ->
	    c++;
	 :: c < N && c != i ->
	    if
	      :: (RN[i].ind[c] == LN[i].ind[c]+1) ->
		 Q[i].ch!c;
	      :: else ->
		 skip;
	    fi;
	    c++;
	 :: else ->
	    break;
       od;
       if
	 :: empty(Q[i].ch) ->
	    skip;
	 :: nempty(Q[i].ch) ->
	    Q[i].ch?c;
	    d_step{
	      havePrivilege[i] = false; // Is it dangerous?
	      havePrivilege[c] = true;
	    }
	    length = len (Q[i].ch);
	    do
	      :: length > 0 ->
		 Q[i].ch?c;
		 Q[i].ch!c;
		 gQ!c;
		 length--;
	      :: else ->
		 break;
	    od;
	    c=0;
	    d_step{
	      do
		:: c < N ->
		   privLN[c] = LN[i].ind[c];
		   c++;
		:: else ->
		   break;
	      od;
	    }
       fi;
       requesting[i] = false;
  od;
}

proctype P2(short i){
  short reqee;
  short reqN;
  short c=0;
  short length;
  do
    :: nempty(inReq[i].ch) ->
       atomic {
	 inReq[i].ch?reqee;
	 inNum[i].ch?reqN;
	 d_step{
	   if
	   :: (RN[i].ind[reqee] < reqN) ->
	      RN[i].ind[reqee] = reqN;
	   :: else ->
	      skip;
	   fi;
	 }
	 if
	   :: havePrivilege[i] && !requesting[i] && RN[i].ind[reqee] == LN[i].ind[reqee]+1 ->	      
	      length = len (Q[i].ch);
	      atomic{ //Dangerous?
		do
		  :: length > 0 ->
		     Q[i].ch?c;
		     Q[i].ch!c;
		     gQ!c;
		     length--;
		  :: else ->
		     break;
		od;
	      }
	      
	      c = 0;
	      d_step{
		do
		  :: c < N ->
		     privLN[c] = LN[i].ind[c];
		     c++;
		  :: else ->
		     break;
		od;
		havePrivilege[i] = false;
		havePrivilege[reqee] = true;
	      }
	   :: else ->
	      skip;
	 fi;
       }
  od;
}

init {
  d_step {
    critical=0;
    r = 0;
    s=0;
    do
      :: r < N ->
	 do
	   :: s < N ->
	      RN[r].ind[s] = -1;
	      LN[r].ind[s] = -1;
	      s++;
	   :: s == N ->
	      s=0;
	      r++;
	      break;
	 od;
	 requesting[r-1]=false;
	 havePrivilege[r-1]=false;
      :: r == N ->
	 r=0;
	 break;
    od;
    havePrivilege[0]=true;
  }
  atomic{
    do
      :: r < N ->
	 run P1(r);  // unreliable processes
	 run P2(r);
	 r++;
      :: else -> break;
    od;
  }
}

ltl critSec{
//  []<>(havePrivilege[0]) &&   []<>(havePrivilege[1]) &&  []<>(havePrivilege[2])
  [](RN[0].ind[0] < 2)
}

//ltl starvation {
  //  [](P2[0]reqN < 2)
//}
