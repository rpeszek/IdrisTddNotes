module Main
import Effects
import Effect.StdIO
import Prelude.Monad
import Sanity.Hello 
import Part1.Sec1_4_5

main : IO ()
main = do  
   run sayHello 
   putStrLn (valToString True 20)
