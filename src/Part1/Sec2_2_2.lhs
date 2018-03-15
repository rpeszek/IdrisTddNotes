|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/N_Part1_Sec2_2_2
|Idris Src: Sec2_3_3.idr

Section 2.2.2. Idris `the` function vs Haskell
==============================================

Idris code example
------------------  
Idris Prelude comes with very cool `the` function reimplemented here as `the'`:
|IdrisRef: Sec2_2_2.idr 

idris repl:
```
*src/Part1/Sec2_2_2> the' Double 3
3.0 : Double
*src/Part1/Sec2_2_2> the' Int 3
3 : Int
*src/Part1/Sec2_2_2> the' String 3
When checking an application of function Part1.Sec2_2_2.the':
        String is not a numeric type
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
```

This approach is clearly not as nice as Idris's. 
I had to declare helper proxies which is ugly.


Other Languages
---------------
Any language that allows to express types as first class values should be able to implement
`the`.  But it is not so easy. 
Here is Groovy console showing what happens in Java
```Groovy
groovy> static <T> T the(Class<T> tc, T t) { return t;}
groovy> (the(Double, 3)).getClass()

Result: class java.lang.Integer
```
This code shows issues with Java implementation of type erasure.  

Hay, maybe Haskell does not have it, but it does not have it correctly! 
 
