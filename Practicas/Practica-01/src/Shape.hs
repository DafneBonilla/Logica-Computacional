module Shape where
    
data Shape = Circle Float | Square Float | Rectangle Float Float | Triangle Float Float | Trapeze Float Float Float
    deriving(Show, Eq)

instance Ord Shape where
    compare shapeA shapeB = compare (area (shapeA)) (area (shapeB))

area :: Shape -> Float
area (Circle a) = pi * a^2
area (Square a) = a^2
area (Rectangle b h) = b * h
area (Triangle b h) = (b * h) / 2
area (Trapeze b t h) = (((b - t) * h) / 2) + (t * h)

perimeter :: Shape -> Float
perimeter (Circle a) = pi * a * 2
perimeter (Square a) = 4 * a
perimeter (Rectangle b h) = 2 * b + 2 * h
perimeter (Triangle b h) = b * 3 -- Damos por hecho que es equilátero
perimeter (Trapeze b t h) = (b + t) + 2 * sqrt(((((b-t)^2) / 4)+ h^2)) -- Damos por hecho que es simétrico
