
module Part2.Sec9_2
import Data.Vect
import Part2.Sec9_1

%default total 

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
     MkWordState : (word : String) ->
                   (missing : Vect letters Char) ->
                   WordState guesses_remaining letters

data Finished : Type where
             Lost : (game : WordState 0 (S letters)) -> Finished
             Won  : (game : WordState (S guesses) 0) -> Finished

processGuess : (letter : Char) -> WordState (S guesses) (S letters) -> Either (WordState guesses (S letters)) (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) = case isElem letter missing of
          Yes prf => Right (MkWordState word (removeElem_auto letter missing)) 
          No contra => Left (MkWordState word missing)

{- the rest is user interface code -}

data ValidInput : List Char -> Type where
     Letter : (c : Char) -> ValidInput [c]

invalidNil : ValidInput [] -> Void
invalidNil (Letter _) impossible

invalidTwo : ValidInput (x :: y :: xs) -> Void
invalidTwo (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No invalidNil
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No invalidTwo

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

covering
readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess:"
               x <- getLine
               case isValidString (toUpper x) of
                  Yes prf => pure (_ ** prf)
                  No contra => do putStrLn "Invalid guess"
                                  readGuess

covering
game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st
             = do (_ ** Letter letter) <- readGuess
                  case processGuess letter st of
                    Left l => do putStrLn "Wrong!"
                                 case guesses of
                                      Z => pure (Lost l)
                                      S k => game l
                    Right r => do putStrLn "Right!"
                                  case letters of
                                       Z => pure (Won r)
                                       S k => game r

{- To execute in repl, idrs repl from src folder, :l this file and use :exec sec_9_2 -}
covering
sec_9_2 : IO ()
sec_9_2 = do result <- game {guesses=2} (MkWordState "Test" ['T', 'E', 'S'])
             case result of
               Lost (MkWordState word missing) =>
                  putStrLn ("You lose. The word was " ++ word)
               Won game =>
                  putStrLn "You win!"
