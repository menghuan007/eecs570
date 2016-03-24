
-- two-state 4-hop VI protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  VC0: 0;                -- low priority
  VC1: 1;
  QMax: 2;
  NumVCs: VC1 - VC0 + 1;
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
  Count: 0..ProcCount;
  MessageType: enum {  GetS,
                       GetM,
                                             
				       PutS,
				       PutM,
				       Put_Ack,
                       
                       Inv,
                       Inv_Ack,
                       
                       Data
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
      				H_S_D }; 						--transient states
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
        -- Send invalidation message here
        Send(Inv, HomeNode.sharers[i], rqst, VC0, rqst.val);
        MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
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
  --cnt := MultiSetCount(i:HomeNode.sharers, true);


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case H_I:
    switch msg.mtype
	
	case GetS:
      HomeNode.state := H_S;
      AddToSharersList(msg.src);
      Send(Data, msg.src, HomeType, VC0, HomeNode.val,HomeNode.sharers);
    case GetM:
      HomeNode.state := H_M;
      HomeNode.owner := msg.src;
      Send(Data, msg.src, HomeType, VC0, HomeNode.val,HomeNode.sharers);
    case PutS:
      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED,HomeNode.sharers);
	case PutM:
	  Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED,HomeNode.sharers);
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_S:
  
    switch msg.mtype
    case GetS:
      Send(Data, msg.src, HomeType, VC0, HomeNode.val,HomeNode.sharers);
      AddToSharersList(msg.src);
    case GetM:
      HomeNode.state := H_M;
      HomeNode.owner := msg.src;
      Send(Data, msg.src, HomeType, VC0, HomeNode.val,HomeNode.sharers);
      SendInvReqToSharers(HomeNode);
	case PutS:
      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED,HomeNode.sharers);
      RemoveFromSharersList(msg.src);
      if (MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) == 0)
      then
      	HomeNode.state := H_I;
      endif;
    case PutM:
	  RemoveFromSharersList(msg.src);
      Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED,HomeNode.sharers);
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_M:
    switch msg.mtype
   
    case GetS:
      HomeNode.state := H_S_D;
      AddToSharersList(HomeNode.owner);
      AddToSharersList(msg.src);
      Send(GetS, HomeNode.owner, HomeType, VC1, UNDEFINED,HomeNode.sharers);
      HomeNode.owner := UNDEFINED;
    case GetM:
    	Send(GetM, HomeNode.owner, HomeType, VC1, UNDEFINED,HomeNode.sharers);
    	HomeNode.owner := msg.src;
    case PutS:
    	Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED,HomeNode.sharers);
    case PutM:
		Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED,HomeNode.sharers);
		if (msg.src == HomeNode.owner)
		then
			HomeNode.val := msg.val;
			HomeNode.owner := UNDEFINED;
			HomeNode.state := H_I;
		endif;
    else
      ErrorUnhandledMsg(msg, HomeType);

  case H_S_D:
    switch msg.mtype
   
	case PutS:
		Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED,HomeNode.sharers);
      	RemoveFromSharersList(msg.src);
	case PutM:
		RemoveFromSharersList(msg.src);
        Send(Put_Ack, msg.src, HomeType, VC1, UNDEFINED,HomeNode.sharers);
	case Data:
		HomeNode.val := msg.val;
		HomeNode.state := H_S;
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
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

  switch ps

  case P_IS_D:
    switch msg.mtype
    case Data:
      ps := P_S;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;
  
  case P_IM_AD:
  	switch msg.mtype
  	case Data:
		if (msg.src = HomeNode)
		then
			p.ack = p.ack + msg.cnt;
			if (p.ack == 0)
				ps := P_M;
			else
				ps := P_IM_A;
			endif;
		else
			ps := P_M;
		endif;
		pv := msg.val;
  	case Inv_Ack:
		p.ack = p.ack - 1;
	endswitch;

  case P_IM_A:
  	switch msg.mtype
  	case Inv_Ack:
		p.ack = p.ack - 1;
		if (p.ack == 0)
			ps := P_M;

  case P_S:
  	switch msg.mtype
  	case Inv:
		Send(Inv_Ack, msg.src, p, VC1, UNDEFINED, UNDEFINED);
		ps := P_I;

  case P_SM_AD:
  	switch msg.mtype
  	case Inv:
		Send(Inv_Ack, msg.src, p, VC1, UNDEFINED, UNDEFINED);
		ps := P_IM_AD;
  	case Data:
		if (msg.src == HomeNode)
		then
			p.ack = p.ack + msg.cnt;
			if (p.ack == 0)
				ps := P_M;
			else
				ps := P_SM_A;
			endif;
		else
			ps := P_M;
		endif;
		pv := msg.val;
  	case Inv_Ack:
		p.ack = p.ack - 1;

  case P_SM_A:
  	switch msg.mtype
  	case Inv_Ack:
		p.ack = p.ack -1;
		if (p.ack == 0)
			ps := P_M;
		endif;

  case P_M:
  	switch msg.mtype
  	case GetS:
		Send(Data, msg.src, p, VC0, pv, UNDEFINED);
		Send(Data, HomeNode, p, VC0, pv, UNDEFINED);
		ps := P_S;
  	case GetM:
		Send(Data, msg.src, p, VC0, pv, UNDEFINED);
		ps := P_I;

  case P_MI_A:
  	switch msg.mtype
  	case GetS:
		Send(Data, msg.src, p, VC0, pv, UNDEFINED);
		Send(Data, HomeNode, p, VC0, pv, UNDEFINED);
		ps := P_SI_A;
  	case GetM:
		Send(Data, msg.src, p, VC0, pv, UNDEFINED);
		ps := P_II_A;
  	case Put_Ack:
		ps := P_I;

  case P_SI_A:
  	switch msg.mtype
  	case Inv:
		Send(Inv_Ack, msg.src, p, VC1, UNDEFINED, UNDEFINED);
		ps := P_II_A;
  	case Put_Ack:
		ps := P_I;

  case P_II_A:
  	switch msg.mtype
  	case Put_Ack:
		ps := P_I;
  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;
  
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
  	rule "store new value"
   	 (p.state = P_I)
    	==>
 		   p.val := v;      
 		   LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
 		   Send(GetM, HomeType, n, VC0, UNDEFINED, UNDEFINED);
 		   p.state := P_IM_AD;
   	 (p.state = P_S)
    	==>
 		   p.val := v;      
 		   LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
 		   Send(GetM, HomeType, n, VC0, UNDEFINED, UNDEFINED);
 		   p.state := P_SM_AD;
  	endrule;
	endruleset;

  rule "read request"
    (p.state = P_I)
  ==>
    Send(GetS, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    p.state := P_IS_D;
  endrule;


  rule "writeback"
    (p.state = P_S)
  ==>
    Send(PutS, HomeType, n, VC0, UNDEFINED, UNDEFINED); 
    p.state := P_SI_A;
    undefine p.val;
    (p.state = P_M)
  ==>
    Send(PutS, HomeType, n, VC1, p.val, UNDEFINED); 
    p.state := P_MI_A;
    undefine p.val;
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

invariant "value in memory matches value of last write, when invalid"
     HomeNode.state = H_I 
    ->
			HomeNode.val = LastWrite;

invariant "values in valid state match last write"
  Forall n : Proc Do	
    (Procs[n].state = P_S) | (Process[n].state = P_M)
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
