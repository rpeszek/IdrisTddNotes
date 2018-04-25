|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part2_Sec9_2
|Idris Src: Sec9_2.idr

Section 9.2 Type safe hangman game vs Haskell
=============================================

Idris code example
------------------  
|IdrisRef: Sec9_2.idr 

Compared to Haskell
-------------------

> {-# LANGUAGE 
>    TemplateHaskell
>    -- , TypeOperators
>    , GADTs
>    , TypeFamilies
>    , DataKinds
>    , PolyKinds
>    , KindSignatures
>    , EmptyCase
>    , RankNTypes
>    , LambdaCase
>    , ScopedTypeVariables -- singletons need it
> #-}
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> 
> module Part2.Sec9_2 where
> import Util.SingVector
> import Util.SingList
> import Part2.Sec8_3
> import Part2.Sec9_1
> import Data.Singletons
> import Data.Singletons.TH
> import Data.Kind (Type)
> import Data.Char (toUpper)

I am trying to avoid type literals and avoid use of type level strings and fighting/learning
with type level list `singletons` syntax.  Type level list (from `Util.SingList`) is used to 
mimic `ValidInput` definition from Idris.   
This is 'by hand' poor man's version: 

> $(singletons [d|
>   data AChar = CA | CB | CC | CD | CE | CF | CG | CH | CI
>              | CJ | CK | CL | CM | CN | CO | CP | CQ | CR
>              | CS | CT | CU | CV | CW | CX | CY | CZ
>     deriving (Read, Show, Eq)
>    
>   |])
> 
> instance DecEqSing AChar where
>      decEqSing SCA SCA = Yes Refl
>      decEqSing SCB SCB = Yes Refl
>      decEqSing SCT SCT = Yes Refl
>      decEqSing SCE SCE = Yes Refl
>      decEqSing SCS SCS = Yes Refl
>      decEqSing SCX SCX = Yes Refl
>      decEqSing _ _ = No undefined -- I am too lazy to do that
>
> charToAChar :: Char -> Either String AChar 
> charToAChar 'A' = Right CA
> charToAChar 'B' = Right CB
> charToAChar 'T' = Right CT 
> charToAChar 'E' = Right CE 
> charToAChar 'S' = Right CS 
> charToAChar 'X' = Right CX
> charToAChar c = Left $ "char " ++ (show c) ++ " not converted"
> 
> stringToAChars :: String -> Either String (List AChar)
> stringToAChars [] = Right LNil
> stringToAChars (c : xs) = do 
>             ac <- charToAChar c
>             axs <- stringToAChars xs
>             Right (LCons ac axs)

Idris dependent typing makes things simpler but, 
other than the use of 'by hand' characters and strings the rest of the code is quite 
similar to Idris!

> data WordState  (guesses_remaining :: Nat) (letters :: Nat) where
>    MkWordState :: forall guesses_remaining (xs :: Vect letters AChar) . 
>                Sing guesses_remaining -> 
>                Sing letters ->
>                String ->
>                SVect xs ->
>                WordState guesses_remaining letters
> 
> data Finished where
>     Lost :: WordState s0 (S letters) -> Finished
>     Won  :: WordState (S guesses) s0 -> Finished
> 
> 
> processGuess :: forall guesses letters (c :: AChar) . 
>                 Sing c -> 
>                 WordState (S guesses) (S letters) -> 
>                 Either (WordState guesses (S letters)) (WordState (S guesses) letters)
> processGuess letter (MkWordState (SS guesses) (SS letters) word missing) = case isElemSing letter missing of
>             Yes prf -> let sres = removeElem (SS letters) letter missing prf 
>                        in case sres of 
>                           MkSomeKnownSizeVect _ newMissing -> Right $ MkWordState (SS guesses) letters word newMissing --(removeElem letter missing prf) 
>             No _ ->  Left $ MkWordState guesses (SS letters) word missing
> 

I use SomeValidInput instead of the dependent pair but the rest is almost identical.

> data ValidInput (chars :: List AChar) where
>      Letter :: forall (c :: AChar) . Sing c -> ValidInput ('LCons c 'LNil)
> 
> data SomeValidInput where
>      SomeValidInput :: ValidInput chars -> SomeValidInput
> 
> withSomeValidInput :: SomeValidInput -> (forall chars. ValidInput chars -> r) -> r
> withSomeValidInput someValidInput f = case someValidInput of 
>          SomeValidInput vinput -> f vinput
> 
> invalidNil :: ValidInput 'LNil -> Void
> invalidNil x = case x of { }
> 
> invalidTwo :: ValidInput ('LCons x ('LCons y xs)) -> Void
> invalidTwo x = case x of { }
> 
> isValidInput :: forall (chars :: List AChar) . Sing chars -> Dec (ValidInput chars)
> isValidInput SLNil = No invalidNil
> isValidInput (SLCons x SLNil) = Yes (Letter x)
> isValidInput (SLCons _ (SLCons _ _)) = No invalidTwo

My 'by hand' characters are not fully supported and I kept the error for not converted stuff.
This also allows for an easy exit from the game.

> readGuess :: IO SomeValidInput
> readGuess = do putStr "Guess:"
>                x <- getLine
>                case stringToAChars (map toUpper x) of
>                   Right acharList -> withSomeSing acharList (\scharList -> 
>                       case isValidInput scharList of 
>                         Yes prf -> return $ SomeValidInput prf  
>                         No _ -> do putStrLn "Invalid guess"
>                                    readGuess
>                      )
>                   Left str -> error $ "unsupported char" ++ str 

There is no real need to split the game into 2 functions but I found it convenient not
having to think much about the `(S guesses) (S letters)` semantics.

> game :: Sing guesses -> Sing letters -> WordState (S guesses) (S letters) -> IO Finished
> game guesses letters st
>         = do someValidInput <- readGuess
>              withSomeValidInput someValidInput (\case 
>                   Letter sletter -> case processGuess sletter st of
>                     Left l -> do putStrLn "Wrong!"
>                                  case guesses of
>                                       SZ -> return (Lost l)
>                                       SS k -> game k letters l
>                     Right r -> do putStrLn "Right!"
>                                   case letters of
>                                        SZ -> return (Won r)
>                                        SS k -> game guesses k r
>                 )
> 
> game' :: WordState (S guesses) (S letters) -> IO Finished
> game' st = case st of 
>         MkWordState (SS guesses) (SS letters) _ _ -> game guesses letters st

The type safe list (`['T', 'E', 'S']` in Idris) is now ugly but I made it!

> sec_9_2 :: IO()
> sec_9_2 
>     = do result <- game' (MkWordState s2 s3 "Test" (SCT `SCons` (SCE `SCons` (SCS `SCons` SNil))))
>          case result of
>                Lost (MkWordState _ _ word missing) ->
>                   putStrLn ("You lose. The word was " ++ word)
>                Won game ->
>                   putStrLn "You win!"

ghci:
```
*Part2.Sec9_2> sec_9_2
Guess:T
Right!
Guess:a
Wrong!
Guess:s
Right!
Guess:e
Right!
You win!
```
