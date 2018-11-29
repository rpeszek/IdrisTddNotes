|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part3_Sec15a_ProcessLib
|Idris Src: Sec15a_ProcessLib.idr

Section 15 Type safe concurrent programming library example vs Haskell
=====================================================================
Concurrent programming is hard. In fact, it took me quite some time 
to create somewhat equivalent version of Idris' `System.Concurrency.Channels`
primitives and getting it to work.

Section 15 of the book shows how dependent types help in creating type safe protocols
on top of less safe primitives.  If the implementation of the protocol
itself is correct, the programs that use it are prevented from race 
conditions.

This section shows the code for the library itself. The next note shows how it is used.

As with the other of my notes, the easiest method or reading this is to open two browser windows side-by-side
and compare Idris and Haskell.

Idris code example
------------------  
|IdrisRef: Sec15a_ProcessLib.idr 

Compared to Haskell
-------------------
I have implemented somewhat close (simplified) equivalents to Idris' `System.Concurrency.Channels`
in
[Control.Concurrent.Primitives](https://github.com/rpeszek/IdrisTddNotes/blob/master/src/Control/Concurrent/Primitives.hs)
included in this project.

> {-# LANGUAGE TemplateHaskell
>       , KindSignatures
>       , DataKinds
>       , GADTs
>       , PolyKinds
>       , TypeFamilies
>       , ScopedTypeVariables
>       , TypeSynonymInstances
>       , StandaloneDeriving
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> {-# OPTIONS_GHC -fwarn-unused-imports #-}
> 
> module Part3.Sec15a_ProcessLib where
> 
> import Control.Concurrent.Primitives 
> -- ^ implemented in this package to mimic Idris' Channels primitives
> import Data.Kind (Type)
> import Data.Singletons.TH
> import Data.SingBased.Nat
> import Prelude (Show(..)) -- because I was lazy
> import Protolude hiding (Nat, forever, show)
> import Control.Monad.Trans.Maybe

Fuel boilerplate to mimic Idris (without any totality assurances, of course):

> data Fuel = Dry | More Fuel
> 
> forever :: Fuel
> forever = More forever

Process library type definitions (DSL definitions) are very similar to Idris, 
I use `singletons` `Sing` when I need arguments that are both value level and type level.
 
> -- type ProcIface reqType = reqType -> Type
> 
> data MessagePID (iface :: reqType -> Type) where
>     MkMessagePID :: PID -> MessagePID iface
> 
> data ProcState = Ready | Sent | Looping
> 
> -- flipped payload type from second position (in Idris version) to the end
> -- making it look more like traditional monad notation
> data Process (iface :: reqType -> Type) (inState:: ProcState) (outState :: ProcState) a where
>      Request :: MessagePID service_iface ->
>                 Sing msg ->
>                 Process iface st st (service_iface msg) 
>      Respond :: (Sing msg -> Process iface Ready Ready (iface msg)) ->
>                 Process iface st Sent (Maybe (Sing msg))
>      Spawn   :: Process service_iface Ready Looping () ->
>                 Process iface st st (Maybe (MessagePID service_iface))
>  
>      Loop    :: Process iface Ready Looping a ->
>                 Process iface Sent Looping a
>      Action  :: IO a -> Process iface st st a
>      UnsafeTest :: IO a -> Process iface st1 st2 a
>      Pure    :: a -> Process iface st st a
>      (:>>=)  :: Process iface st1 st2 a -> (a -> Process iface st2 st3 b) ->
>                 Process iface st1 st3 b
> infixl 1  :>>=
>
> (>>:) ::  Process iface st1 st2 a 
>            -> Process iface st2 st3 b
>            -> Process iface st1 st3 b
> (>>:) m k = m :>>= \ _ -> k  
> infixl 1  >>:
> 
> data NoRecv (v :: Void) where
>   
> type Service iface a = Process iface 'Ready 'Looping a
> type Client a = Process NoRecv Ready Ready a

Interpreter definition follows.
Idris has a nice exit syntax for `Nothing` maybe cases.  
This uses the transformer MaybeT instead to avoid boilerplate. 

> runT :: MonadIO m => MVar [Channel] -> Fuel -> Process iface in_state out_state t -> MaybeT m t
> runT mchs _ (Request (MkMessagePID pid) smsg)
>             = do chan <- MaybeT . liftIO . connect mchs $ pid
>                  liftIO $ unsafeSend chan smsg
>                  x <- liftIO $ unsafeRecv chan
>                  pure x
> 
> runT mchs fuel (Respond calc) = do 
>               channel <- MaybeT . liftIO . listen $ mchs
>               msg <- liftIO $ unsafeRecv channel
>               res <- runT mchs fuel (calc msg)
>               liftIO $ unsafeSend channel res
>               pure (Just $ msg)
> 
> runT mchs (More fuel) (Loop proc) = runT mchs fuel proc
> 
> runT mchs fuel (Spawn proc) = do 
>               pid <- liftIO $ spawn mchs (
>                    do runMaybeT $ runT mchs fuel proc
>                       pure ())
>               pure ((Just (MkMessagePID pid)))
> 
> runT _ _ (Action act) = do 
>                 res <- liftIO act
>                 pure res
> runT _ _ (UnsafeTest act) = do 
>                 res <- liftIO act
>                 pure res
> runT _ _ (Pure val) = pure val
> runT mchs fuel (act :>>= next) = runT mchs fuel act >>= runT mchs fuel . next
> runT _ Dry _ = MaybeT . pure $ Nothing
> 
> run :: Fuel -> Process iface in_state out_state t -> IO (Maybe t)
> run fuel p = (newMVar []) >>= (\mchs -> runMaybeT $ runT mchs fuel p) 

Simple test example to see that it works. `ListAction` example is in the next note.
It is worth noting that implementing kind `iface :: reqType -> Type` is not as elegant
as in Idris. (see next note for more discussion).

> -- test example
> $(singletons [d|
>  data NatAction = PlusA Nat Nat | ReplayA Nat deriving Show
>  |])
> 
> deriving instance Show (SNatAction a)
> 
> data NatActionType :: NatAction -> Type where
>    PlusAT   ::  Nat -> NatActionType ('PlusA n m)
>    -- ^ 'n' 'm' are picked automatically by compiler
>    ReplayAT ::  Nat -> NatActionType ('ReplayA n)
>    -- ^ 'n' is picked automatically by compiler
>     
> deriving instance  Show (NatActionType a)
>  
> serviceNatAction :: Service NatActionType ()
> serviceNatAction =  Respond (\msg -> case msg of
>                           SPlusA m n -> 
>                                Pure $ PlusAT $ (fromSing m) `plus` (fromSing n) 
>                           SReplayA n -> 
>                                Pure $ ReplayAT (fromSing n)) 
>             >>:  Loop serviceNatAction
> 
> clientNatAction :: Client ()
> clientNatAction = 
>               Spawn serviceNatAction :>>= (\natProcessorJ -> 
>                case natProcessorJ of 
>                  Just natProcessor -> 
>                           Request natProcessor (SReplayA s4) :>>= (\res -> Action (print $ res)) >>: 
>                           Request natProcessor (SPlusA s4 s1) :>>= (\res -> Action (print $ res))
>                  Nothing -> Action (putStrLn "failed")
>             )


ghci (contains a tracing message I added in `spawn` implementation):  
```
*Part3.Sec15a_ProcessLib> run (More $ More Dry) clientNatAction
New thread created ThreadId 273
ReplayAT (S (S (S (S Z))))
PlusAT (S (S (S (S (S Z)))))
Just ()
```
