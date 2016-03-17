
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
         );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
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
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        -- Send invalidation message here
        Send(Inv, HomeNode.sharers[i], rqst, VC0, rqst.val);
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
      HomeNode.owner := msg.src;
      Send(Data, msg.src, HomeType, VC1, HomeNode.val);
    case GetM:
      HomeNode.state := H_M;
      HomeNode.owner := msg.src;
      Send(Data, msg.src, HomeType, VC1, HomeNode.val);
    case PutS:
      HomeNode.owner := msg.src;
      Send(Put_Ack, msg.src, HomeType, VC1, HomeNode.val);
	case PutM:
	
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_S:
    Assert (IsUndefined(HomeNode.owner) = false) 
       "HomeNode has no owner, but line is Valid";

    switch msg.mtype
    case GetS:
      Send(RecallReq, HomeNode.owner, HomeType, VC0, UNDEFINED);
      HomeNode.owner := msg.src; --remember who the new owner will be
            
    case GetM:
    	assert (msg.src = HomeNode.owner) "Writeback from non-owner";
      HomeNode.state := H_Invalid;
      HomeNode.val := msg.val;
      Send(WBAck, msg.src, HomeType, VC1, UNDEFINED);
      undefine HomeNode.owner

	case PutS:
      Send(RecallReq, HomeNode.owner, HomeType, VC0, UNDEFINED);
      HomeNode.owner := msg.src; --remember who the new owner will be
    case PutM:
      Send(RecallReq, HomeNode.owner, HomeType, VC0, UNDEFINED);
      HomeNode.owner := msg.src; --remember who the new owner will be
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case H_M:
    switch msg.mtype
   
    case GetS:
      Assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
      HomeNode.state := H_Valid;
      HomeNode.val := msg.val;
      Send(ReadAck, HomeNode.owner, HomeType, VC1, HomeNode.val);

    case GetM:
    	msg_processed := false; -- stall message in InBox
    case PutS:
    
    case PutM:

    else
      ErrorUnhandledMsg(msg, HomeType);

  case H_S_D:
    switch msg.mtype
   
    case GetS:
      Assert (!IsUnDefined(HomeNode.owner)) "owner undefined";
      HomeNode.state := H_Valid;
      HomeNode.val := msg.val;
      Send(ReadAck, HomeNode.owner, HomeType, VC1, HomeNode.val);

    case GetM:
    	msg_processed := false; -- stall message in InBox

	case PutS:
	case PutM:
	case Data:
	
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
  case P_I:

    switch msg.mtype
    case RecallReq:
      Send(WBReq, msg.src, p, VC1, pv);
      Undefine pv;
      ps := P_Invalid;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_Pending:

    switch msg.mtype
    case ReadAck:
      pv := msg.val;
      ps := P_Valid;
    case RecallReq:
    	msg_processed := false; -- stall message in InBox
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;


  case P_IS_D:

    switch msg.mtype
    case WBAck:
      ps := P_Invalid;
      undefine pv;
    case RecallReq:				-- treat a recall request as a Writeback acknowledgement
      ps := P_Invalid;
      undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
		endswitch;
  
  case P_IM_AD:
  
  	switch msg.mtype
  	case GetS:
  	
  	case GetM:
  	
  	case Data:
  	
  	case Inv_Ack:
  
  case P_IM_A:
  	switch msg.mtype
  	case GetS:
  	
  	case GetM:
  	
  	case Inv_Ack:
  
  case P_S:
  	switch msg.mtype
  	case Inv:
  
  case P_SM_AD:
  	switch msg.mtype
  	case GetS:
  	
  	case GetM:
  	
  	case Inv:
  	
  	case Data:
  	
  	case Inv_Ack:
  
  case P_SM_A:
  	switch msg.mtype
  	case GetS:
  	
  	case GetM:
  	
  	case Inv_Ack:
  
  case P_M:
  	switch msg.mtype
  	case GetS:
  	
  	case GetM:
  
  case P_MI_A:
  	switch msg.mtype
  	case GetS:
  	
  	case GetM:
  	
  	case Put_Ack:
  
  case P_SI_A:
  	switch msg.mtype
  	case Inv:
  	
  	case Put_Ack:
  
  case P_II_A:
  	switch msg.mtype
  	case Put_Ack:

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
   	 (p.state = P_Valid)
    	==>
 		   p.val := v;      
 		   LastWrite := v;  --We use LastWrite to sanity check that reads receive the value of the last write
  	endrule;
	endruleset;

  rule "read request"
    p.state = P_Invalid 
  ==>
    Send(ReadReq, HomeType, n, VC0, UNDEFINED);
    p.state := PT_Pending;
  endrule;


  rule "writeback"
    (p.state = P_Valid)
  ==>
    Send(WBReq, HomeType, n, VC1, p.val); 
    p.state := PT_WritebackPending;
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
