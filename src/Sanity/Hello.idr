module Sanity.Hello
import Effects
import Effect.StdIO
||| Defining this in another file using the STDIO effect is not that practical,
||| but it should help illustrate the project structure.
public export
sayHello : Eff () [STDIO]
sayHello = putStrLn "Hello, world!"
