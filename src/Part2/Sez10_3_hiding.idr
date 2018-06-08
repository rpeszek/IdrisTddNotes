
module Part2.Sez10_3_hiding


export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double
export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export
circle : Double -> Shape
circle = Circle

-- export public
data ShapeView : Shape -> Type where
     STriangle : ShapeView (triangle base height)
     SRectangle : ShapeView (rectangle width height)
     SCircle : ShapeView (circle radius)

shapeView : (s : Shape) -> ShapeView s
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle


area : Shape -> Double
area s with (shapeView s)
  area (triangle base height) | STriangle = 0.5 * base * height
  area (rectangle width height) | SRectangle = width * height
  area (circle radius) | SCircle = pi * radius * radius

{-
*Part2/Sez10_3_hiding> area (circle 1)
3.141592653589793 : Double
-}
