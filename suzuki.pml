#define N 2

/* Request message type */
typedef REQUEST{
  chan ch = [N] of {byte, byte};
}

/* Used to create an array of arrays */
typedef Array{
  byte ind[N];
}

/* Queue datatype */
typedef Queue {
  chan ch = [N] of {byte};
  bool inQ[N];
}

/* PRIVILEGE message type */
typedef PRIVILEGE {
  chan ch = [N] of {Queue, Array};
}

hidden byte r=0;
Array RN[N]; /* "local" copies of RN and LN, have to be visible for both P1 and P2 */
Array LN[N];
bool havePrivilege[N]; /* True when ones own is set to true. Only someone with privilege alters this */
bool requesting[N]; /* True when a process is requesting */
byte counter; /* Used when checking for mutual exclusion */

Queue Q[N];

PRIVILEGE priv; /* The privilege channel, only the current privilege-holder may read this */
REQUEST req[N]; /* Request channels */

proctype P1(byte i){
  byte c=0; /* Counter */
  do
    :: 1 ->
       d_step{ requesting[i] = true; c=0; }
       if
	 :: havePrivilege[i] ->	skip;	    
	 :: else ->
	    /* Request the privilege */
	    atomic {
	      RN[i].ind[i]++;
	      do
	      :: else -> break;
		:: c == i -> c++; skip;
	      :: c < N && c != i ->
		 req[c].ch!i, RN[i].ind[i]; c++;
	      od;
	    }
	    /* Wait for privilege */
	    if
	      :: havePrivilege[i] ->
		 priv.ch?Q[i], LN[i];
	    fi;
       fi;
       
progress:
crit:  
       d_step{
	 counter++;c=0;
	 LN[i].ind[i] = RN[i].ind[i];
	 /* add requesting processes to the queue */
       do
	 :: else -> break;
	 :: c==i -> c++; skip;
	 :: c<N && c!=i ->
	    if
	      :: else -> skip;
	      :: !Q[i].inQ[c] && RN[i].ind[c] == LN[i].ind[c] + 1 ->
		 Q[i].ch!c;
		 Q[i].inQ[c]=true;
	    fi; c++;
	 od;
	 
	 counter--;

	 /* If any process is requesting, send the privilege to that process */
	 if
	   :: nempty(Q[i].ch) ->
	      Q[i].ch?c;
	      Q[i].inQ[c]=false;
	      priv.ch!Q[i], LN[i];
	      havePrivilege[i] = false;
	      havePrivilege[c] = true;
	   :: empty(Q[i].ch) -> skip;
	 fi;
       }

       requesting[i] = false;
  od;
end:
}

proctype P2(byte i){
  chan rreq = req[i].ch;
  xr rreq; /* P2 is the only process reading from this channel */
  byte reqee, reqN; /* (node identifier, request identifier) */
  byte c=0;
end:
	// This does not allow for messages to be received in another order than they were sent. This could be solved by randomely jumping over a message randomely, and put it in the end of the queue again.
  do    
    :: nempty(req[i].ch) ->
       d_step {
	 rreq?reqee,reqN;
	 /* Chose the highest value as the right value for RN */
	 if
	   :: RN[i].ind[reqee] < reqN ->
	      RN[i].ind[reqee] = reqN;
	   :: else -> skip;		
	 fi;

	 /* If P1 is not requesting and another process does, send the privilege */
	 if
	   :: havePrivilege[i] && !requesting[i] && RN[i].ind[reqee] == LN[i].ind[reqee]+1 ->
	      priv.ch!Q[i], LN[i];
	      havePrivilege[i]=false;
	      havePrivilege[reqee]=true;
	   :: else -> skip;
	 fi;
       }
  od;
}

init {
  havePrivilege[0]=true;
  atomic{
    do
      :: r < N ->
	 run P1(r);  // unreliable processes
	 run P2(r);
	 r++;
      :: else -> break;
    od;
    r=0;
  }
}


/* Uncomment to check mutual exclusion */
/*
ltl mutex {
  (counter < 2) U (RN[0].ind[0] > 2 || RN[1].ind[1] > 2 || RN[2].ind[2] > 2)
}
*/

/* Uncomment to check for deadlock freedom */
/*
ltl deadlock {
  !timeout U (RN[0].ind[0] > 2 || RN[1].ind[1] > 2 || RN[2].ind[2] > 2)
}
*/

/* Uncomment to check for starvation freedom */
/*
ltl starvation {
  (requesting[0] -> <>(havePrivilege[0])) U (RN[0].ind[0] > 1 || RN[1].ind[1] > 2) // || RN[2].ind[2] > 2)
}
*/
