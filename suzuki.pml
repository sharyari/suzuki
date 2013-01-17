#define N 3
#define _empty(_ch) (len(_ch) == 0)
#define _nempty(_ch) (len(_ch) != 0)

typedef Arraychan {
  chan ch = [N] of {short};
}

typedef Reqchan{
  chan ch = [N] of {short, short};
}

typedef ArrayArray{
  short ind[N];
}

// This is incremented when entering critical section, and decremented when exiting. Debugging purposes
short critical;

ArrayArray RN[N]; // "local" copies of RN and LN, have to be visible for both P1 and P2
ArrayArray LN[N]
bool havePrivilege[N]; // True when ones own is set to true. Only someone with privilege alters this
short r,s;  // For looping and such
bool requesting[N]; //True when a process is requesting
Arraychan Q[N]; // Everyone has a local queue
chan gQ = [N] of {short}; // This global channel is for sending privileges 

chan test = [5] of {};


bool inGQ[N];
ArrayArray inQ[N];
Reqchan req[N]; // These two come in pairs. A REQUEST is sent by adding the index here 

short privLN[N]; // Second parameter in a privilege message

proctype P1(short i){
  short c=0;
  short length=0;
  do
    :: true ->
       requesting[i] = true;
       if
	 :: !(havePrivilege[i]) ->
	    atomic {
	      RN[i].ind[i]++;
	      do
		:: c < N && c != i ->
		   req[c].ch!i,(RN[i].ind[i]);
		   assert(RN[i].ind[i] < 1);
		   c++;
		:: c == i ->
		   c++;
		:: else ->
		   break;
	      od;
	    }
	    if
	      :: havePrivilege[i] ->
		 critical++;
		 do
		   :: nempty(Q[i].ch) ->
		      Q[i].ch?c;
		   :: empty(Q[i].ch) ->
		      skip;
		 od;
		 length = len (gQ);
		 atomic {
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
			inQ[i].ind[c] = inGQ[c];
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
       d_step{
	 LN[i].ind[i] = RN[i].ind[i];
	 c = 0;
       }
       do
	 :: c == i ->
	    c++;
	 :: c < N && c != i ->
	    if
	      :: (RN[i].ind[c] > LN[i].ind[c]) ->
		 if
		   :: (!inQ[i].ind[c]) ->
		      Q[i].ch!c;
		      inQ[i].ind[c] = true;
		   :: else ->
		      skip;
		 fi;
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
	    Q[i].ch?r;
	    inQ[i].ind[r] = false;
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
		   inGQ[c] = inQ[i].ind[c];
		:: else ->
		   break;
	      od;
	    }
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
	    d_step{
	      havePrivilege[i] = false;
	      havePrivilege[r] = true;
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
    :: nempty(req[i].ch) ->
       atomic {
	 req[i].ch?reqee,reqN;
	 d_step{
	   if
	     :: (RN[i].ind[reqee] < reqN) ->
		RN[i].ind[reqee] = reqN;
	     :: else ->
		skip;
	   fi;
	 }
	 if
	   :: havePrivilege[i] && !requesting[i] && RN[i].ind[reqee] > LN[i].ind[reqee] ->	      
	      length = len (Q[i].ch);
	      atomic
	      { //Dangerous?
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
	      c=0;
	      d_step{
		do
		  :: c < N ->
		     inGQ[c] = inQ[i].ind[c];
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
//  []<>(havePrivilege[2]) &&   []<>(havePrivilege[1]) //&&  []<>(havePrivilege[2])
  [](critical  < 100)
}

//ltl starvation {
  //  [](P2[0]reqN < 2)
//}
