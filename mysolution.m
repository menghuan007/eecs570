
-- two-state 4-hop VI protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;
  VC3: 3;
  QMax: 2;
  NumVCs: VC3 - VC0 + 1;
  NetMax: ProcCount+1;
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: VC0..NumVCs-1;
  Count: -10..10;
  MessageType: enum {  GetS,
                       GetM,
                                             
				       PutS,
				       PutM,
				       Put_Ack,
                       
                       Inv,
                       Inv_Ack,
                       
                       Data,
                       NoData
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification;
      -- the destination is indicated by which array 
      -- entry in the Net the message is placed
      vc: VCType;
      val: Value;
	  cnt: Count;
    End;

  HomeState:
    Record
      state: enum { H_I, H_S, H_M, 					--stable states
      				H_S_D, H_S_D2, H_M_D};			--transient states
      owner: Node;	
      sharers: multiset [ProcCount] of Node;		--No need for sharers in this protocol, but this is a good way to represent them
      val: Value;
    End;

  ProcState:
    Record
      state: enum { P_I, P_S, P_M,					--stable states
                  P_IS_D, P_IM_AD, P_IM_A, P_SM_AD, 
				  P_SM_A, P_MI_A, P_SI_A, P_II_A }; --transient states
      val: Value;
	  ack: Count;
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;
  -- One multiset for each destination - messages are arbitrarily reordered by the multiset
  InBox: array [Node] of array [VCType] of Message;
  -- If a message is not processed, it is placed in InBox, blocking that virtual channel
  msg_processed: boolean;
  LastWrite: Value; 
  -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	       dst:Node;
	       src:Node;
         vc:VCType;
         val:Value;
		 cnt:Count;
         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  msg.cnt	:= cnt;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

-- These aren't needed for Valid/Invalid protocol, but this is a good way of writing these functions
Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

-- Sends a message to all sharers except rqst
Procedure SendInvreqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then
	    RemoveFromSharersList(n);
        -- Send invalidation message here
        Send(Inv, n, rqst, VC2, UNDEFINED, MultiSetCount(i:HomeNode.sharers, true));
      endif;
    endif;
  endfor;
End;


Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;  -- for counting sharers
Begin
-- Debug output may be helpful:
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

  -- The line below is not needed in Valid/Invalid protocol.  However, the 
  -- compiler barfs if we put this inside a switch, so it is useful to
  -- pre-calculate the sharer count here
  cnt := MultiSetCount(i:HomeNode.sharers, true);


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case H_I:
    switch msg.mtype
	
	case GetS:
      HomeNode.state := H_S;
      Send(Data, msg.src, HomeType, VC0, HomeNode.val, cnt);
      AddToSharersList(msg.src);
    case GetM:
      HomeNode.state := H_M;
      HomeNode.owner := msg.src;
      Send(Data, msg.src, HomeType, VC0, HomeNode.val, cnt);
    case PutS:
      Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED, cnt);
	case PutM:
	  Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED, cnt);
	case Data:
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_S:
    switch msg.mtype
    case GetS:
      AddToSharersList(msg.src);
      Send(Data, msg.src, HomeType, VC0, HomeNode.val,cnt);
    case GetM:
      SendInvreqToSharers(msg.src);
      if (IsSharer(msg.src))
      then
      	RemoveFromSharersList(msg.src);
      	Send(Data, msg.src, HomeType, VC0, HomeNode.val,cnt-1);
      else
      	Send(Data, msg.src, HomeType, VC0, HomeNode.val,cnt);
      endif;
      HomeNode.state := H_M;
      HomeNode.owner := msg.src;
	case PutS:
	  RemoveFromSharersList(msg.src);
      Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
      if (cnt = 0)
      then
      	HomeNode.state := H_I;
      endif;
    case PutM:
	  RemoveFromSharersList(msg.src);
      Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
    case Data:
    case NoData:
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_M:
    switch msg.mtype
   
    case GetS:
      Send(GetS, HomeNode.owner, msg.src, VC1, UNDEFINED,cnt);
      AddToSharersList(HomeNode.owner);
      AddToSharersList(msg.src);
      --HomeNode.owner := UNDEFINED;
      HomeNode.state := H_S_D;
    case GetM:
    	Send(GetM, HomeNode.owner, msg.src, VC3, UNDEFINED,cnt);
    	HomeNode.owner := msg.src;
    case PutS:
    	Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
    case PutM:
		Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
		if (msg.src = HomeNode.owner)
		then
			HomeNode.val := msg.val;
			HomeNode.owner := UNDEFINED;
			HomeNode.state := H_I;
		endif;
	case Data:
		msg_processed := false;
	case NoData:
		msg_processed := false;
    else
      ErrorUnhandledMsg(msg, HomeType);
	endswitch;
	
  case H_S_D:
    switch msg.mtype
    case GetS:
    	msg_processed := false;
    case GetM:
    	msg_processed := false;
	case PutS:
		RemoveFromSharersList(msg.src);
		Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
	case PutM:
		RemoveFromSharersList(msg.src);
        Send(Put_Ack, msg.src, HomeType, VC2, UNDEFINED,cnt);
        if (HomeNode.owner = msg.src)
        then
        	HomeNode.state := H_S;
        	HomeNode.val := msg.val;
        	HomeNode.owner := UNDEFINED;
        else
        	Send(Data, HomeNode.owner, HomeType, VC0, HomeNode.val, cnt); 
        endif;
	case Data:
		HomeNode.val := msg.val;
		HomeNode.state := H_S;
		HomeNode.owner := UNDEFINED;
	case NoData:
		Send(Data, HomeNode.owner, HomeType, VC0, HomeNode.val, cnt);
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;
  else
    ErrorUnhandledState();
  endswitch;
End;


Procedure ProcReceive(msg:Message; p:Proc);
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at proc "; put p; put "\n";

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val do
  alias pa:Procs[p].ack do

  switch ps
  case P_I:
  	switch msg.mtype
    case Inv:
      Send(Inv_Ack, msg.src, p, VC2, UNDEFINED, 0);
    case GetS:
      --Send(NoData, HomeType, p, VC2, UNDEFINED, 0);
    case GetM:
      Send(NoData, HomeType, p, VC0, UNDEFINED, 0);
    case Data:
    case Put_Ack:
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;
  case P_IS_D:
    switch msg.mtype
    case Inv:
   	  msg_processed := false;
    case Data:
      ps := P_S;
      pv := msg.val;
    case GetS:
      --Send(NoData, HomeType, p, VC2, UNDEFINED, 0);
    case GetM:
      Send(NoData, HomeType, p, VC2, UNDEFINED, 0);
    case Put_Ack:
    else
      ErrorUnhandledMsg(msg, p);
	endswitch;
	
  case P_IM_AD:
  	switch msg.mtype
  	case GetS:
  		msg_processed := false;
  	case GetM:
  		msg_processed := false;
  	case Data:
  		pv := msg.val;
		if (msg.src = HomeType)
		then
			Procs[p].ack := Procs[p].ack + msg.cnt;
			if (Procs[p].ack = 0)
			then
				ps := P_M;
				LastWrite := pv;
			else
				ps := P_IM_A;
			endif;
		else
			ps := P_M;
			LastWrite := pv;
		endif;
  	case Inv_Ack:
		Procs[p].ack := Procs[p].ack - 1;
	case Inv:
	case Put_Ack:
	else
      ErrorUnhandledMsg(msg, p);
	endswitch;
	
  case P_IM_A:
  	switch msg.mtype
  	case GetS:
  		msg_processed := false;
  	case GetM:
  		msg_processed := false;
  	case Inv_Ack:
		Procs[p].ack := Procs[p].ack - 1;
		if (Procs[p].ack = 0)
		then
			ps := P_M;
			LastWrite := pv;
		endif;
	case Data:
	case Put_Ack:
	else
      ErrorUnhandledMsg(msg, p);
	endswitch;
	
  case P_S:
  	switch msg.mtype
  	case Inv:
		Send(Inv_Ack, msg.src, p, VC2, UNDEFINED, 0);
		undefine pv;
		ps := P_I;
	case GetS:
		Send(Data, msg.src, p, VC0, pv, 0);
	case GetM:
		Send(Data, msg.src, p, VC0, pv, 0);
	case Data:
	else
      ErrorUnhandledMsg(msg, p);
	endswitch;
	
  case P_SM_AD:
  	switch msg.mtype
  	case GetS:
  		msg_processed := false;
  	case GetM:
  		msg_processed := false;
  	case Inv:
		Send(Inv_Ack, msg.src, p, VC2, UNDEFINED, 0);
		ps := P_IM_AD;
  	case Data:
		pv := msg.val;
		if (msg.src = HomeType)
		then
			Procs[p].ack := Procs[p].ack + msg.cnt;
			if (Procs[p].ack = 0)
			then
				ps := P_M;
				LastWrite := pv;
			else
				ps := P_SM_A;
			endif;
		else
			ps := P_M;
			LastWrite := pv;
		endif;
  	case Inv_Ack:
		Procs[p].ack := Procs[p].ack - 1;
	else
      ErrorUnhandledMsg(msg, p);
	endswitch;

  case P_SM_A:
  	switch msg.mtype
  	case GetS:
  		msg_processed := false;
  	case GetM:
  		msg_processed := false;
  	case Inv_Ack:
		Procs[p].ack := Procs[p].ack -1;
		if (Procs[p].ack = 0)
		then
			ps := P_M;
			LastWrite := pv;
		endif;
	else
      ErrorUnhandledMsg(msg, p);
	endswitch;

  case P_M:
  	switch msg.mtype
  	case GetS:
		Send(Data, msg.src, p, VC0, pv, 0);
		Send(Data, HomeType, p, VC0, pv, 0);
		ps := P_S;
  	case GetM:
		Send(Data, msg.src, p, VC0, pv, 0);
		undefine pv;
		ps := P_I;
	case Data:
	else
      ErrorUnhandledMsg(msg, p);
	endswitch;

  case P_MI_A:
  	switch msg.mtype
  	case GetS:
		Send(Data, msg.src, p, VC0, pv, 0);
		Send(Data, HomeType, p, VC0, pv, 0);
		ps := P_SI_A;
  	case GetM:
		Send(Data, msg.src, p, VC0, pv, 0);
		ps := P_II_A;
  	case Put_Ack:
  		undefine pv;
		ps := P_I;
	case Data:
	else
      ErrorUnhandledMsg(msg, p);
	endswitch;

  case P_SI_A:
  	switch msg.mtype
  	case Inv:
		Send(Inv_Ack, msg.src, p, VC2, UNDEFINED, 0);
		ps := P_II_A;
  	case Put_Ack:
  		undefine pv;
		ps := P_I;
	case GetS:
	case GetM:
	case Data:
	else
      ErrorUnhandledMsg(msg, p);
	endswitch;

  case P_II_A:
  	switch msg.mtype
  	case Put_Ack:
  		undefine pv;
		ps := P_I;
	else
      ErrorUnhandledMsg(msg, p);
    endswitch;
  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();
  endswitch;
  
  endalias;
  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)

ruleset n:Proc Do
  alias p:Procs[n] Do
  
	ruleset v:Value Do
	
	rule "store new value P_I"
   	 (p.state = P_I)
    	==>
 		   p.val := v;
 		   Send(GetM, HomeType, n, VC3, UNDEFINED, 0);
 		   p.state := P_IM_AD;
  	endrule;
  	
  	rule "store new value P_M"
   	 (p.state = P_M)
    	==>
 		   p.val := v;      
 		   LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
	 endrule;

  	rule "store new value P_S"
   	 (p.state = P_S)
    	==>
 		   p.val := v;
 		   Send(GetM, HomeType, n, VC3, UNDEFINED, 0);
 		   p.state := P_SM_AD;
  	endrule;
  	endruleset;

  rule "read request P_I"
    (p.state = P_I)
  ==>
    Send(GetS, HomeType, n, VC1, UNDEFINED, 0);
    p.state := P_IS_D;
  endrule;


  rule "writeback P_S"
    (p.state = P_S)
  ==>
    Send(PutS, HomeType, n, VC1, UNDEFINED, 0); 
    p.state := P_SI_A;
    endrule;
    
  rule "writeback P_M"
    (p.state = P_M)
  ==>
    Send(PutM, HomeType, n, VC0, p.val, 0);
    --Send(Data, HomeType, n, VC0, p.val, 0); 
    p.state := P_MI_A;
  endrule;

  endalias;
endruleset;

-- Message delivery rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do
    alias box:InBox[n] do

		-- Pick a random message in the network and delivier it
    rule "receive-net"
			(isundefined(box[msg.vc].mtype))
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
			endif;

			if ! msg_processed
			then
				-- The node refused the message, stick it in the InBox to block the VC.
	  		box[msg.vc] := msg;
			endif;
	  
		  MultiSetRemove(midx, chan);
	  
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  

	-- Try to deliver a message from a blocked VC; perhaps the node can handle it now
	ruleset vc:VCType do
    rule "receive-blocked-vc"
			(! isundefined(InBox[n][vc].mtype))
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(InBox[n][vc]);
      else
        ProcReceive(InBox[n][vc], n);
			endif;

			if msg_processed
			then
				-- Message has been handled, forget it
	  		undefine InBox[n][vc];
			endif;
	  
    endrule;
  endruleset;

endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

	For v:Value do
  -- home node initialization
  HomeNode.state := H_I;
  undefine HomeNode.owner;
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := P_I;
    Procs[i].ack   := 0;
    undefine Procs[i].val;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  HomeNode.state = H_I
  ->
      IsUndefined(HomeNode.owner);

invariant "values in valid state match last write"
  Forall n : Proc Do	
    Procs[n].state = P_S | Procs[n].state = P_M
    ->
			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
	end;
	
invariant "value is undefined while invalid"
  Forall n : Proc Do	
     Procs[n].state = P_I
    ->
			IsUndefined(Procs[n].val)
	end;
	
-- Here are some invariants that are helpful for validating shared state.

invariant "modified implies empty sharers list"
  HomeNode.state = H_M
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = H_I
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do	
     HomeNode.state = H_S | HomeNode.state = H_I
    ->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state match memory"
  Forall n : Proc Do	
     HomeNode.state = H_S & Procs[n].state = P_S
    ->
			HomeNode.val = Procs[n].val
	end;
