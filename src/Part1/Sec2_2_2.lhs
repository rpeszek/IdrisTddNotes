|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/idrVsHs_Part1_Sec2_2_2
|Idris Src: Sec2_3_3.idr

Section 2.2.2. Idris `the` function vs Haskell vs Java
======================================================

Idris code example
------------------  
Idris Prelude comes with a very cool `the` function reimplemented here as `the'`.
This function allows to resolve polymorphic or overloaded data constructors:
|IdrisRef: Sec2_2_2.idr 

idris repl:
```
*src/Part1/Sec2_2_2> the' Double 3
3.0 : Double
*src/Part1/Sec2_2_2> the' Int 3
3 : Int
*src/Part1/Sec2_2_2> the' Int "Test"
(input):1:1-15:When checking an application of function Part1.Sec2_2_2.the':
        Type mismatch between
                String (Type of "Test")
        and
                Int (Expected type)

*src/Part1/Sec2_2_2> the' (List Int) [1,2,3]
[1, 2, 3] : List Int
*src/Part1/Sec2_2_2> the' (List _) [1,2,3]
[1, 2, 3] : List Integer
*src/Part1/Sec2_2_2> :module Data.Vect
*src/Part1/Sec2_2_2 *Data/Vect> the' (Vect _ _) [1,2,3]
[1, 2, 3] : Vect 3 Integer
```

Compared to Haskell
-------------------
To do something similar, Haskell would need a value level representation of types. 

> module Part1.Sec2_2_2 where
> import Data.Proxy
>
> the :: Proxy a -> a -> a
> the _ x = x
>
> double :: Proxy Double 
> double = Proxy 
>
> int :: Proxy Int 
> int = Proxy 
>
> string :: Proxy String 
> string = Proxy 
>
> list :: Proxy a -> Proxy ([a])
> list _ = Proxy
>
> numList :: Num a => Proxy ([a])
> numList = Proxy

ghci:
```
*Part1.Sec2_2_2> :t the int 3
the intProxy 3 :: Int
*Part1.Sec2_2_2> :t the double 3
the doubleProxy 3 :: Double
*Part1.Sec2_2_2> :t the double "test"

<interactive>:1:17: error:
    • Couldn't match expected type ‘Double’ with actual type ‘[Char]’
    • In the second argument of ‘the’, namely ‘"test"’
      In the expression: the double "test"

*Part1.Sec2_2_2> :t the (list int) [1,2,3]
the (list int) [1,2,3] :: [Int]
*Part1.Sec2_2_2> :t the numList [1,3,4]
the numList [1,3,4] :: Num a => [a]
```
(Vector equivalent not shown because I am just lazy, besides Haskell does not have
data constructor overloading.)

This approach is clearly not as nice as Idris's. 
I had to declare helper proxies which is ugly.


Java
----
Any language that can express types as first class values should be able to implement
`the`.  Java comes to mind because it has the `Class<T>` type.  But it is not so easy. 
Here is Groovy console showing what happens in Java
```Groovy
groovy> static <T> T the(Class<T> tc, T t) { return t;}
groovy> (the(Double, 3)).getClass()

Result: class java.lang.Integer
```
The same concept, fully equivalent code, only it does not work. 
This can be blamed on Java type erasure.  
Incidentally, Haskell has full type erasure, Java only erases type variables. 
Type erasure concept in itself is not what is wrong.
 
