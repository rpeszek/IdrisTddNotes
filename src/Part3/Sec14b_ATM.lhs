|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Part3_Sec14b_ATM
|Idris Src: Sec14b_ATM.idr

Section 14.2 Type Safe ATM protocol example vs Haskell
=======================================================
This program is about converting a powerful dependently typed 
state machine pattern to Haskell. The pattern is about defining 
a DSL with instructions parameterized by startState and a function that evaluates
computation result producing endState

`Dsl : (res : Type) -> DslState -> (res -> DslState) -> Type`

and providing monad-like binding that enforces that 
endState of a step matches the beginState of the next.

```
     Pure : (res : ty) -> Dsl ty (state_fn res) state_fn     
     (>>=) : Dsl a state1 state2_fn ->
             ((res : a) -> Dsl b (state2_fn res) state3_fn) ->
             Dsl b state1 state3_fn
```

Idris code example
------------------  
|IdrisRef: Sec14b_ATM.idr 

Compared to Haskell
-------------------
I am using `Unsafe.Coerce`. This is probably hard to do without it.
The `unsafeCoerce` is needed to transform the bind (`:>>=`) part of DSL to IO
(see the comment below). 

I am also simplifying things and using `Nat` to define `pin`.

> {-# LANGUAGE TemplateHaskell
>       , KindSignatures
>       , DataKinds
>       , GADTs
>       , PolyKinds
>       , TypeInType 
>       , TypeOperators 
>       , TypeFamilies
>       , StandaloneDeriving
>       , UndecidableInstances 
>       , ScopedTypeVariables
> #-}
> 
> module Part3.Sec14b_ATM where
> 
> import Data.Kind (Type)
> import Data.Singletons.TH
> import Data.Promotion.TH
> import Data.Singletons.Prelude
> import Data.SingBased.Vect
> import Data.SingBased.Nat
> import Unsafe.Coerce -- needed in binding DSL to IO
> import Control.Exception
> 
> {- to keep everything singleton I need singleton Unit too-}
> $(singletons [d|
>  data ATMState = Ready | CardInserted | Session
>  data PINCheck = CorrectPIN | IncorrectPIN
>  data Unit = MkUnit
>  |])
> 
> $(promote [d|
>  checkPin :: PINCheck -> ATMState
>  checkPin CorrectPIN = Session
>  checkPin IncorrectPIN = CardInserted
>  |])
> 
> {- simplified one char numeric pin -}
> type PIN = Nat
> 
> readPIN :: IO (SomeSing PIN)
> readPIN = readNat 
> 
> readNat :: IO (SomeSing Nat)
> readNat = do x <- getLine
>              let mxi = readMaybe x :: Maybe Integer 
>              case mxi of
>                 Nothing -> do 
>                   putStrLn $"Invalid entry " ++ show x ++ " try again"
>                   readNat
>                 Just xi -> do
>                   let xn = integerToNat xi
>                   return $ withSomeSing xn SomeSing 
> 
> readMaybe :: Read a => String -> Maybe a
> readMaybe s = case reads s of
>                  [(val, "")] -> Just val
>                  _           -> Nothing
>
> testPIN = SS (SS SZ)
> 
> data HasCard (s :: ATMState) where
>      HasCI      :: HasCard CardInserted
>      HasSession :: HasCard Session
> 
> data ATMCmd (res :: k) (s :: ATMState) (f :: k ~> ATMState) where
>      InsertCard :: ATMCmd 'MkUnit 'Ready   (ConstSym1 'CardInserted)
>      {- Idris can use auto-implicit here -}
>      EjectCard  :: HasCard state ->
>                    ATMCmd 'MkUnit  state   (ConstSym1 'Ready)
>      GetPIN     :: ATMCmd (p :: PIN) 'CardInserted (ConstSym1 'CardInserted) 
>      CheckPIN   :: forall (p :: PIN) (check :: PINCheck) . 
>                    Sing p -> ATMCmd check 'CardInserted CheckPinSym0     
>      GetAmount  :: ATMCmd (n :: Nat) state (ConstSym1 state)
>      Dispense   :: SNat n -> ATMCmd 'MkUnit 'Session (ConstSym1 'Session)
>      Message    :: String -> ATMCmd 'MkUnit state (ConstSym1 state)
> 
>      Pure       :: forall (res :: k) (state_fn :: k ~> ATMState). Sing res -> ATMCmd res (state_fn @@ res) state_fn
>      {- note this has to be cross-kind! -}
>      (:>>=)     :: forall (a :: k1) (b :: k2) (state1 :: ATMState) (state2_fn :: k1 ~> ATMState) (state3_fn :: k2 ~> ATMState).
>                    ATMCmd a state1 state2_fn ->
>                    (Sing a -> ATMCmd b (state2_fn @@ a) state3_fn) ->
>                    ATMCmd b state1 state3_fn
>
> (>>:) ::  forall k (a :: k1) (b :: k2) (state1 :: ATMState) (state2_fn :: k1 ~> ATMState) (state3_fn :: k2 ~> ATMState).
>           ATMCmd a state1 state2_fn
>           -> ATMCmd b (state2_fn @@ a) state3_fn
>           -> ATMCmd b state1 state3_fn
> (>>:) m k    = m :>>= \ _ -> k  

Note that `(:>>=)` goes across kinds. This is important because it limits the domain scope 
of type level state functions as well as the domain scope of `Sing a` (it increases type precision).

Note that DSL definition becames more complex with the use of `singletons` GADT-zed type level 
functions (`~>` and `@@`) and 'symbols'.

* `type (~>) a b = TyFun a b -> Type` 
* `type (@@) (a :: k1 ~> k) (b :: k1) = Apply a b :: k`

In particular, these are needed for type level partial application.  Haskell type families do not allow
for partial application. 

Here is how the DSL is used:

> insertEject :: ATMCmd 'MkUnit 'Ready (ConstSym1 'Ready)
> insertEject =  InsertCard >>: EjectCard HasCI 
> 
> atm :: ATMCmd 'MkUnit 'Ready (ConstSym1 'Ready)
> atm =  InsertCard >>: GetPIN :>>=
>        (\ pin -> Message "Checking Card" >>:
>                  CheckPIN pin) :>>=
>        (\ pinOK -> case pinOK of
>           SCorrectPIN -> GetAmount :>>= (\ cash -> 
>               Dispense cash >>: 
>               EjectCard HasSession >>: 
>               Message "Please remove your card and cash"
>            )
>           SIncorrectPIN -> EjectCard HasCI >>:
>                            Message "Incorrect PIN. Please remove your card and cash"
>         )

The interpreter:

> ioUnit :: IO (SomeSing Unit) 
> ioUnit = return $ SomeSing SMkUnit
> 
> runATM :: forall (res :: k) instate outstate_fn. ATMCmd res instate outstate_fn -> IO (SomeSing k)
> runATM InsertCard = do putStrLn "Please insert your card (press enter)"
>                        x <- getLine
>                        ioUnit
> runATM (EjectCard _) = 
>                 do putStrLn "Card ejected"
>                    ioUnit
> runATM GetPIN = 
>                 do putStr "Enter PIN: "
>                    readPIN
> runATM (CheckPIN pin) = 
>                 if fromSing pin == fromSing testPIN
>                 then return $ SomeSing SCorrectPIN
>                 else return $ SomeSing SIncorrectPIN
> runATM GetAmount = 
>                 do putStr "How much would you like? "
>                    readNat
> runATM (Dispense amount) = 
>                 do putStrLn ("Here is " ++ show amount)
>                    ioUnit
> runATM (Message msg) = 
>                 do putStrLn msg
>                    ioUnit
> runATM (Pure res) = return $ SomeSing res

The case match on `:>>=` constructor is where I need `unsafeCoerce`. 
This should be safe because I am mapping a stricter definitions of 
`ATMCmd (res::k)` DSL to looser `IO (SomeSing k)`.   
_TODO_ Maybe using something like a `Tapeable` would give me some way to do 
type equality proofs here??  At this time, I DUNNO.

> runATM (x :>>= f) = 
>                 do ax <- runATM x 
>                    case ax of
>                      SomeSing sax -> runATM (f $ unsafeCoerce sax)
> 

ghci:

```
*Part3.Sec14b_ATM Data.Singletons.Prelude> runATM atm
Please insert your card (press enter)

Enter PIN: 2
Checking Card
How much would you like? 5
Here is S (S (S (S (S Z))))
Card ejected
Please remove your card and cash
*Part3.Sec14b_ATM Data.Singletons.Prelude> runATM atm
Please insert your card (press enter)

Enter PIN: 5
Checking Card
Card ejected
Incorrect PIN. Please remove your card and cash
```
