module Part3.Sec14a_DoorJam

data DoorState = DoorOpen | DoorClosed

data DoorResult = OK | Jammed

data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
     Open : DoorCmd DoorResult DoorClosed 
                               (\res => case res of
                                             OK => DoorOpen
                                             Jammed => DoorClosed)
     Close : DoorCmd () DoorOpen (const DoorClosed)
     RingBell : DoorCmd () DoorClosed (const DoorClosed)

     Display : String -> DoorCmd () state (const state)

     ||| Pure also sets the initial state
     Pure : (res : ty) -> DoorCmd ty (state_fn res) state_fn
     
     ||| >>= enforces type safe state transitions
     ||| notice how state2_fn defines initial state for second command
     (>>=) : DoorCmd a state1 state2_fn ->
             ((res : a) -> DoorCmd b (state2_fn res) state3_fn) ->
             DoorCmd b state1 state3_fn

logOpen : DoorCmd DoorResult DoorClosed 
                             (\res => case res of
                                           OK => DoorOpen
                                           Jammed => DoorClosed)
logOpen = do Display "Trying to open the door"
             OK <- Open | Jammed => do Display "Jammed"
                                       Pure Jammed
             Display "Success"
             Pure OK  -- since previous state is OK
{- 
pureOK : DoorCmd DoorResult
                 DoorOpen
                 (\res => case res of   OK => DoorOpen Jammed => DoorClosed)
-}

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do RingBell
              OK <- Open | Jammed => Display "Door Jammed" --pattern-matching bindings
              Display "Glad To Be Of Service"
              Close
