module Main
-- import Effects
-- import Effect.StdIO
-- import Prelude.Monad
-- import Sanity.Hello 

-- Needed for Idris build script!
import Part1.Sec1_4_5
import Part1.Sec2_2_2_the
import Util.MiniParser
import Part2.Sec3_2_3_gen
import Part2.Sec4_2_2_gen
import Part2.Sec5_3_3_dpair
import Part2.Sec6_1_1_tyfunc
import Part2.Sec6_2_1_adder
import Part2.Sec6_2_2_printf
import Part2.Sec6_3_datastore
import Part2.Sec6_3b_datastore
import Part2.Sec8_1_eqproof
import Part2.Sec8_2_5_vappd
import Part2.Sec8_2z_reverse
import Part2.Sec8_3_deceq
import Part2.Sec9_1_elem
import Part2.Sec9_2_hangman
import Part2.Sez10_1_views
import Part2.Sez10_2a_snoc
import Part2.Sez10_2b     
import Part2.Sez10_2e     
import Part2.Sez10_3_hiding
import Part3.Sec14a_DoorJam
import Part3.Sec14b_ATM
import Part3.Sec15a_ProcessLib
import Part3.Sec15b_ProcessList 
import Play.FunctorLaws      

main : IO ()
main = sec6_3b
   --do  
   -- run sayHello 
   -- putStrLn (valToString True 20)
