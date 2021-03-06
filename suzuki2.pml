#define N 2
#define L 2
#define _empty(_ch) (len(_ch) == 0)
#define _nempty(_ch) (len(_ch) != 0)

/* Request message type */
typedef REQUEST{
  chan ch = [N] of {byte, short};
}

/* Used to create an array of arrays */
typedef Array{
  short ind[N];
}

/* Queue datatype */
typedef Queue {
  chan ch = [N] of {short};
  bool inQ[N];
}

/* PRIVILEGE message type */
typedef PRIVILEGE {
  chan ch = [N] of {Queue, Array};
}

/* Reply channel */
chan reply[N] = [N] of {bool};


Array RN[N]; /* "local" copies of RN and LN, have to be visible for both P1 and P2 */
Array LN[N];
bool havePrivilege[N]; /* True when ones own is set to true. Only someone with privilege alters this */
bool requesting[N]; /* True when a process is requesting */
byte replycount[N]; /* Reflects the number of reply messages received */
short counter; /* Used when checking for mutual exclusion */

Queue Q[N];

PRIVILEGE priv; /* The privilege channel, only the current privilege-holder may read this */
REQUEST req[N]; /* Request channels */


proctype P1(byte i){
  byte c; /* Counter */
  bool nreceived=0; /* This is set to one when N-1 reply messages have been received */
  do
    :: 1 ->
       d_step{c=0; requesting[i] = true;}
	atomic {
       if
	 :: havePrivilege[i] ->	 skip;	
	 :: else ->
	    /* Request the privilege */	    
	      RN[i].ind[i] = (RN[i].ind[i]+1) % L;
	      nreceived=0;	    
	      do
		:: else ->  break;
		:: c == i ->  c++; skip;
		:: c < N && c != i ->
		   req[c].ch!i, RN[i].ind[i]; c++;
	      od;	    
	    /* Wait for privilege */
	    if
	      :: havePrivilege[i] ->
		 priv.ch?Q[i], LN[i];
	    fi;
       fi;
}
progress:   
    d_step {
      /* Read the queue if needed */
       if
	 :: nempty(priv.ch) ->
	    priv.ch?Q[i], LN[i];
	 :: empty(priv.ch) ->
	    skip;
       fi;
       

	 counter++; // debugging
	 LN[i].ind[i] = RN[i].ind[i];
       }

	atomic {
       /* Wait if this is the L:th round, and replies have not allready been received */
       if /* manipulate the below line to reproduce the found deadlock */
	 :: (RN[i].ind[i] == L-1) && !nreceived-> 
	    if
	      :: (replycount[i] == N-1) ->
		 replycount[i] = 0;
		 nreceived=1;
	    fi;
	 :: else -> skip;
       fi;
crit:  }
       /* Add requesting processes to the queue */
       d_step {
	 c=0;
	 do
	   :: else -> counter--;break;
	   :: c==i -> c++; skip;
	   :: c<N && c!=i ->
	      if
		:: !Q[i].inQ[c] && RN[i].ind[c] == (LN[i].ind[c] + 1) % L->
		   Q[i].ch!c;
		   Q[i].inQ[c]=true;
		:: else -> skip;
	      fi;
	      c++;
	 od;

	 /* If any process is requesting, send the privilege to that process */
	 if
	   :: nempty(Q[i].ch) ->
	      Q[i].ch?c;
	      Q[i].inQ[c]=false;
	      priv.ch!Q[i], LN[i];
	      havePrivilege[i] = false;
	      havePrivilege[c] = true;
	   :: empty(Q[i].ch) ->
	      skip;
	 fi;
	 requesting[i] = false;
       }
  od;
}

proctype P2(byte i){
  chan rreq = req[i].ch; 
  xr rreq; /* P2 is the only process reading from this channel */
  byte reqee, reqN; /* (node identifier, request identifier) */
  byte requestcount[N];
  do    
/* This could be used to simulate processes being received out of order */
/*    :: nempty(req[i].ch) ->

progressdummy:
       d_step{
	 rreq?reqee,reqN;
	 req[i].ch!reqee,reqN;
       }*/
    :: nempty(req[i].ch) ->
       d_step {
	 rreq?reqee,reqN;
	 requestcount[reqee]++;
	 /* If this is the Lth request, send a REPLY message*/
	 if
	   :: requestcount[reqee] == L ->
	      reply[reqee]!1;
	      requestcount[reqee] = 0;
	   :: else -> skip;
	 fi;

	 /* Chose the right value of RN */
	 if
	   :: requestcount[reqee] == 1 ->
	      RN[i].ind[reqee] = reqN;
	   :: else ->
	      if
		:: RN[i].ind[reqee] < reqN ->
		   RN[i].ind[reqee] = reqN;
		:: else ->
		   skip;
	      fi;
	 fi;
	 /* If P1 is not requesting and another process does, send privilege*/
	 if
	   :: havePrivilege[i] && !requesting[i] && RN[i].ind[reqee] == (LN[i].ind[reqee]+1) % L ->
	      priv.ch!Q[i], LN[i];
	      havePrivilege[i]=false;
	      havePrivilege[reqee]=true;
	   :: else ->
	      skip;
	 fi;
       }
  od;
}

proctype P3(short i){
  replycount[i]=0;
  bool trash;
  chan rreply = reply[i];
  xr rreply; /* P3 is the only process reading from this channel */
  do
    :: nempty(rreply) ->
       d_step{
	 rreply?_; /* "read" the channel */
	 replycount[i]++;
       }
  od;
}


init {
  byte i,j;
  do
    :: i<N ->
       j=0;
       do
	 :: j < N ->
	    RN[i].ind[j] = -1;
	    LN[i].ind[j] = -1;
	    j++;
	 :: else -> break;
       od;
       i++;
    :: else -> break;
  od;
  i=0;
  havePrivilege[0]=true;
  atomic{
    do
      :: i < N ->
	 run P1(i);  // unreliable processes
	 run P2(i);
	 run P3(i);
	 i++;
      :: else -> break;
    od;
    i=0;
  }
end: 
}


#define hP0 havePrivilege[0]
#define hP1 havePrivilege[1]
#define hP2 havePrivilege[2]
#define r0 requesting[0]
#define r1 requesting[1]
#define r2 requesting[2]


/* Uncomment to check Mutual exclusion */
/*
ltl mutex {
  [](counter < 2)
}
*/

/* Uncomment to check for deadlock freedom */
/*
ltl deadlock {
  []!timeout
}
*/

/* Uncomment to check for starvation freedom */

ltl starvation {
  [](<>[]r1 -> []<>hP1 && <>[]r0 -> []<>hP0) // && <>[]r2 -> []<>hP2)
}

 