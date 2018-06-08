||| This is almost exact copy from the book with some naming adjusted
||| see
||| https://github.com/edwinb/TypeDD-Samples/blob/master/Chapter15/ProcessLib.idr
module Part3.Sec15a_ProcessLib

import System.Concurrency.Channels

%default total

export
data MessagePID : (iface : reqType -> Type) -> Type where
     MkMessage : PID -> MessagePID iface

public export
NoRecv : Void -> Type
NoRecv = const Void

public export
data ProcState = Ready | Sent | Looping


{-
                     Respond
                       ->
            Respond   |  |      Loop
    Ready   ------->  Sent   --------> Looping
                             <--------
                              Respond             
-}

public export
data Process : (iface : reqType -> Type) ->
               Type -> ProcState -> ProcState -> Type where
     ||| returns service_iface defined type, does not change state
     Request : MessagePID service_iface ->
               (msg : service_reqType) ->
               Process iface (service_iface msg) st st
     ||| CPS handler returns Process in in Ready state, iface is not specified but
     ||| iface (iface msg) is contrained, intersting this can be used with Pure  
     Respond : ((msg : reqType) -> Process iface (iface msg) Ready Ready) ->
               Process iface (Maybe reqType) st Sent
     ||| allows Looping service (argument) to process arbitrary state
     Spawn : Process service_iface () Ready Looping ->
             Process iface (Maybe (MessagePID service_iface)) st st

     ||| used by service to loop
     Loop : Inf (Process iface a Ready Looping) ->
            Process iface a Sent Looping
     ||| Encodes IO as process
     Action : IO a -> Process iface a st st
     Pure : a -> Process iface a st st
     (>>=) : Process iface a st1 st2 -> (a -> Process iface b st2 st3) ->
             Process iface b st1 st3

public export
data Fuel = Dry | More (Lazy Fuel)

export partial
forever : Fuel
forever = More forever

export total
run : Fuel -> Process iface t in_state out_state -> IO (Maybe t)
run fuel (Request {service_iface} (MkMessage process) msg)
          = do Just chan <- connect process
                    | _ => pure Nothing
               ok <- unsafeSend chan msg
               if ok then do Just x <- unsafeRecv (service_iface msg) chan
                                  | Nothing => pure Nothing
                             pure (Just x)
                     else pure Nothing
run fuel (Respond {reqType} calc)
          = do Just sender <- listen 1
                    | Nothing => pure (Just Nothing)
               Just msg <- unsafeRecv reqType sender
                    | Nothing => pure (Just Nothing)
               Just res <- run fuel (calc msg)
                    | Nothing => pure Nothing
               unsafeSend sender res
               pure (Just (Just msg))
run (More fuel) (Loop proc) = run fuel proc
run fuel (Spawn proc) = do Just pid <- spawn (do run fuel proc
                                                 pure ())
                                | Nothing => pure (Just Nothing)
                           pure (Just (Just (MkMessage pid)))
run fuel (Action act) = do res <- act
                           pure (Just res)
run fuel (Pure val) = pure (Just val)
run fuel (act >>= next) = do Just x <- run fuel act
                                  | Nothing => pure Nothing
                             run fuel (next x)
run Dry _ = pure Nothing

public export
Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a Ready Looping

public export
Client : Type -> Type
Client a = Process NoRecv a Ready Ready

partial export
runProc : Process iface () in_state out_state -> IO ()
runProc proc = do run forever proc
                  pure ()
