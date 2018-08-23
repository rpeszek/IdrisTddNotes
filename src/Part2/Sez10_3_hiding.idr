
module Part2.Sez10_3_hiding

-- export type, not constructors (symilar to typical approach in Haskell)
export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

-- export these instead of constructors (symilar to typical approach in Haskell)
-- only in Idris we can pattern match on these!
export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export
circle : Double -> Shape
circle = Circle

-- exports view (with contructors for client to pattern match on) instead of 
-- Shape constructors
-- note exported functions used on the RHS of constructors
public export
data ShapeView : Shape -> Type where
     STriangle : ShapeView (triangle base height)
     SRectangle : ShapeView (rectangle width height)
     SCircle : ShapeView (circle radius)

export
shapeView : (s : Shape) -> ShapeView s
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle

-- example client code 
-- can use elaborate pattern match that reflects on the RHS of ShapeView 
-- using exported functions
area : Shape -> Double
area s with (shapeView s)
  area (triangle base height) | STriangle = 0.5 * base * height
  area (rectangle width height) | SRectangle = width * height
  area (circle radius) | SCircle = pi * radius * radius

{-
*Part2/Sez10_3_hiding> area (circle 1)
3.141592653589793 : Double
-}
