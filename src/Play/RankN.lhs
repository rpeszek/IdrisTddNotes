|Markdown version of this file: https://github.com/rpeszek/IdrisTddNotes/wiki/Play_RankN
|Idris Src: RankN.idr

Higher Ranks in Idris vs Haskell
=====================================
Rank-n types are a very interesting Haskell language capability.
Is Idris capable of supporting rank-n?  This note shows Haskell code first. 
Matching Idris' code follows.

A short intro note
------------------   
I want to share this pragmatic intuition about rank-n types.  
Rank-n is about understanding the very nature of parametric polymorphism.  
Logicians and PLT theorists refer to it as System F or Girard–Reynolds type system.  
Great reference with theoretical background: [TAPL book, chapter 23 Universal Types](https://www.cis.upenn.edu/~bcpierce/tapl/)

Polymorphic functions such as ```id :: forall a . a -> a``` can be used by caller
with any type `a`. The implementation, however, cannot assume anything about `a`.  
_(In lambda calculus terms - system F terms - as a caller 
I want to be able to apply a given type (say `Int`) to type level expression 
`forall a. T(a)` resulting in `T(Int)`)_

I want to be able to make such polymorphism first class, for example, 
I want polymorphic functions to be valid function arguments. I want to be able 
to define function types using polymorphic building blocks.  Here is an example:
```
example :: (forall a. a -> a) -> String
```
This is exactly what 'System F' and rank-n is about.  

_SideNote_: A native approach would be to define 
```naive :: forall a . (a -> a) -> String```
Such defined `native` does not restrict it argument to only polymorphic functions, 
rather it is itself polymorphic.  
This complies just fine:
```
fInt :: Int -> Int 
fInt = (+1)

wrong = naive idInt 
```
and since the caller can make arbitrary decision about `a` the implementation cannot 
(these will not compile:)
```
naive f = f "hello"             -- compilation error
naive f = show . f $ (1 :: Int) -- compilation error
```
What we want is exactly the opposite!
This inversion of control is reminiscent of existential quantification and is
often used in Haskell for exactly this purpose (like in STMonad `runST`).

This type application on a function argument (implementation specifies/restricts 
type on polymorphic input argument) translates on high level to this algebraic rule
(maybe not very formally correct) :
```
(forall x. T x) -> a 
reduces to: 
exists x . T x -> a
```
_End SideNote_

It turns out that types with polymorphic building blocks are not easy to 
implement and it is good to know where the polymorphic 
building blocks are placed.  
The question is 'how negative' these positions are.

_Side Note_:  In the context of rank-n I like to think that:   
In `a -> b` `a` is in negative position `b` in positive.    
In `(a -> b) -> c` `c` has positive position,  `a` and `b` are in negative.
`a` has even more negative position than `b`.

Enter ranked types.  
Rank-n types allow localized type variable quantification,
`n` identifies how negative is the position where the quantifier can be placed. 

Quoting TAPL book (see reference above):  
"A type is said to be of rank 2 if no path from its root to a∀ quantifier passes 
to the left of 2 or more arrows, when the type is drawn as a tree."  
This definition generalizes to ranks higher than 2 hence the rank-n term.

Type checker can get in trouble with things like type reconstruction (inference)
(which is undecidable for rank > 2). 

Idris code example
------------------  
|IdrisRef: FunctorLaws.idr 

In Haskell
----------
I have found some issues (using 8.2.2) with support for rank-n (as shown in the code comments)
I think these are caused by limited support for impredicative polymorphism in Haskell.
(see [impredicative in ghc user guide](https://downloads.haskell.org/~ghc/master/users-guide/glasgow_exts.html#impredicative-polymorphism)).
There is an `ImpredicativeTypes` pragma but it does not appear to help here.

> {-# LANGUAGE RankNTypes #-}
>
> module Play.RankN where 
>
> -- type application example (rank 2)
> example2 :: (forall a . a -> a) -> (Int, String) 
> example2 f = (f 2, f "hello")
>
> testExample2 = example2 id
>
> -- | another rank 2 example
> example2' :: (forall a . a -> a) -> Int
> -- this will not compile:
> --   Couldn't match type ‘a0 -> a0’ with ‘forall a. a -> a’
> -- example2' = fst . example2 
> --   neither will this:
> -- example2' f = fst . example2 $ f
> example2' f = fst (example2 f)
>
> testExample2' = example2' id
> 
> -- | rank 3 example (note caller and implementation are again reversed)
> example3 :: ((forall a . a -> a) -> Int) -> String
> -- ghc has problems compiling: 
> -- example3 f = show . f $ id  
> example3 f = show (f id)
>
> testExample3 = example3 example2'

and these will not compile (as expected)

```
badTestExample2 = example2 (++ "")     --^ (++ "") :: String -> Strings
example3 f = show (f (++ ""))          --^ (++ "") :: String -> Strings
```

Note `example3` implementation uses ad-hoc `show` that is not valid for all types.  
This generalizes System F type application to typeclass constraints. 

ghci:
```
*Play.RankN> testExample2
(2,"hello")
*Play.RankN> testExample2'
2
*Play.RankN> testExample3
"2"
```

Idris code example
------------------ 
Idris can use 
[implicit type arguments](http://docs.idris-lang.org/en/latest/tutorial/miscellany.html) 
to accomplish equivalent functionality.   
Note Idris does not seem to have the same problems as Haskell does.
 
|IdrisRef: RankN.idr 

idris repl:
```
*Play/RankN> example2 id
(2, "hello") : (Int, String)
*Play/RankN> example3 example2'
"2" : String
```
