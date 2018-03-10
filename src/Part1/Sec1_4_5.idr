module Part1.Sec1_4_5

public export
StringOrInt : Bool -> Type
StringOrInt x = case x of
       True => Int
       False => String 

getStringOrInt : (x : Bool) -> StringOrInt x
getStringOrInt x = case x of
          True => 10
          False => "Hello"

public export
valToString : (x : Bool) -> StringOrInt x -> String
valToString x val = case x of
          True => cast val
          False => val
