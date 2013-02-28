#define N 2
#define L 2
#define _empty(_ch) (len(_ch) == 0)
#define _nempty(_ch) (len(_ch) != 0)

typedef Arraychan {
  chan ch = [N] of {short};
}

typedef REQUEST{
  chan ch = [N] of {byte, short};
}

typedef Array{
  short ind[N];
}

typedef Queue {
  chan ch = [N] of {short};
  bool inQ[N];
}

typedef PRIVILEGE {
  chan ch = [N] of {Queue, Array};
}

chan reply[N] = [N] of {bool};

hidden short r=0;
Array RN[N]; // "local" copies of RN and LN, have to be visible for both P1 and P2
Array LN[N];
bool havePrivilege[N]; // True when ones own is set to true. Only someone with privilege alters this
bool requesting[N]; //True when a process is requesting

byte replycount[N];

short counter;

Queue Q[N];

PRIVILEGE priv;
REQUEST req[N];


proctype P1(byte i){
  byte c;
  bool nreceived=0;
  do
    :: 1 ->
       d_step{c=0; requesting[i] = true;}
       if
	 :: havePrivilege[i] ->	    skip;	    
	 :: else ->
	    atomic {
	      RN[i].ind[i] = (RN[i].ind[i]+1) % L;
	      //nreceived=0;	    
	      do
		:: else ->  break;
		:: c == i ->  c++; skip;
		:: c < N && c != i ->
		   req[c].ch!i, RN[i].ind[i]; c++;
	      od;	    }
wait:	    
	    if
	      :: havePrivilege[i] ->
		 priv.ch?Q[i], LN[i];
	    fi;
       fi;
progress:   
//accept:
       if
	 :: nempty(priv.ch) ->
	    priv.ch?Q[i], LN[i];
	 :: empty(priv.ch) ->
	    skip;
       fi;

       
crit:  
       d_step {
	 counter++; // debugging
	 LN[i].ind[i] = RN[i].ind[i];
       }
       if
	 :: (RN[i].ind[i] == L-1) -> //&& !nreceived->
	    if
	      :: (replycount[i] == N-1) ->
		 replycount[i] = 0;
		// nreceived=1;
	    fi;
	 :: else -> skip;
       fi;
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

	 if
	   :: nempty(Q[i].ch) ->
	      havePrivilege[i] = false;
	      Q[i].ch?c;
	      Q[i].inQ[c]=false;
	      priv.ch!Q[i], LN[i];
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
  xr rreq;
  byte reqee, reqN;
  byte requestcount[N];
  do    
    :: nempty(req[i].ch) ->
progressdummy:
       d_step{
	 rreq?reqee,reqN;
	 req[i].ch!reqee,reqN;
       }
    :: nempty(req[i].ch) ->
       d_step {
	 rreq?reqee,reqN;
	 requestcount[reqee]++;
	 if
	   :: requestcount[reqee] == L ->
	      reply[reqee]!1;
	      requestcount[reqee] = 0;
	   :: else -> skip;
	 fi;

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
  xr rreply;
  do
    :: nempty(rreply) ->
       d_step{
	 rreply?_;
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
  
  havePrivilege[0]=true;
  atomic{
    do
      :: r < N ->
	 run P1(r);  // unreliable processes
	 run P2(r);
	 run P3(r);
	 r++;
      :: else -> break;
    od;
    r=0;
  }
end: 
}
#define hP0 havePrivilege[0]
#define hP1 havePrivilege[1]
#define hP2 havePrivilege[2]
#define r0 requesting[0]
#define r1 requesting[1]
#define r2 requesting[2]


ltl critSec {
    []!timeout
//  <>[]np_ //noprog
// <>[]r1 -> []<>hP1  // live or no prog??
//  []<>hP1 && []<>hP2 && []<>hP0
//   [](counter < 2) //safety
}
