#define N 4
#define _empty(_ch) (len(_ch) == 0)
#define _nempty(_ch) (len(_ch) != 0)

typedef Arraychan {
  chan ch = [N] of {byte};
}

typedef REQUEST{
  chan ch = [N] of {byte, byte};
}

typedef Array{
  byte ind[N];
}

typedef Queue {
  chan ch = [N] of {byte};
  bool inQ[N];
}

typedef PRIVILEGE {
  chan ch = [N] of {Queue, Array};
}


Array RN[N]; // "local" copies of RN and LN, have to be visible for both P1 and P2
Array LN[N];
bool havePrivilege[N]; // True when ones own is set to true. Only someone with privilege alters this
bool requesting[N]; //True when a process is requesting

byte critical;

Queue Q[N];

PRIVILEGE priv;

REQUEST req[N];


proctype P1(byte i){
  byte c=0;
  do
    :: 1 ->
       d_step{
	 c=0;
	 requesting[i] = true;
       }
       if
	 :: havePrivilege[i] ->
	    skip;	    
	 :: else ->
	    atomic {
	      RN[i].ind[i]++;
	      do
	      :: else ->
		 break;
	      :: c == i ->
		 c++;
		 skip;
	      :: c < N && c != i ->
		 req[c].ch!i, RN[i].ind[i];
		 c++;
	      od;
	    }
	    if
	      :: havePrivilege[i] ->
		 priv.ch?Q[i], LN[i];
	    fi;
  fi;

crit:
       critical++;
       
       d_step{
	 LN[i].ind[i] = RN[i].ind[i];
	 c=0;
       
       do
	 :: else ->
	    break;
	 :: c==i ->
	    c++;
	    skip;
	 :: c<N && c!=i ->
	    if
	      :: else ->
		 skip;
	      :: !Q[i].inQ[c] && RN[i].ind[c] == LN[i].ind[c] + 1 ->
		 Q[i].ch!c;
		 Q[i].inQ[c]=true;
	    fi;
	    c++;
       od;

       critical--;


	 if
	   :: nempty(Q[i].ch) ->
	      Q[i].ch?c;
	      priv.ch!Q[i], LN[i];
	      Q[i].inQ[c]=false;
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
  byte reqee;
  byte reqN;
  byte c=0;
  do
    :: nempty(req[i].ch) ->
       d_step {
	 req[i].ch?reqee,reqN;
	   if
	     :: RN[i].ind[reqee] < reqN ->
		RN[i].ind[reqee] = reqN;
	     :: else ->
		skip;		
	   fi;

	 if
	   :: havePrivilege[i] && !requesting[i] && RN[i].ind[reqee] == LN[i].ind[reqee]+1 ->
	      priv.ch!Q[i], LN[i];
	      havePrivilege[i]=false;
	      havePrivilege[reqee]=true;
	   :: else ->
	      skip;
	 fi;
       }
  od;
}

init {
  havePrivilege[0]=true;
  byte r=0;
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
//  []<>(havePrivilege[1]) &&   []<>(havePrivilege[0]) //&&  []<>(havePrivilege[2])
  []!(RN[0].ind[0] > 50 && RN[0].ind[3] > 5)
}
