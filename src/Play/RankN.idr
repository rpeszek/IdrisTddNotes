
module Play.RankN 

example2 : ({a : Type} -> a -> a) -> (Int, String) 
example2 f = (f 2, f "hello")

example2' : ({a : Type} -> a -> a) -> Int
example2' = fst . example2 
-- also compiles and works fine
-- example2' f = fst . example2 $ f

example3 : (({a : Type} -> a -> a) -> Int) -> String
example3 f = show . f $ id  
