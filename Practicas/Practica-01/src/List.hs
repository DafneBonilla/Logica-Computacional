module List where

-- Usando la función < reverse > obtenemos la reversa de una cadena para compararla con la original.
isPal :: String -> Bool
isPal text = text == reverse text

concat' :: [[a]] -> [a]
concat' [] = []
concat' (head : queue) = head ++ concat' queue

-- Usando la función < foldr > concatenamos la lista de derecha a izquierda.
reversaFr :: [a] ->[a]
reversaFr = foldr(\x acc -> acc ++ [x]) []


-- La función pascalN usa recursión, tomando los casos base 0 y 1. En realidad, se pudo haber dejado solo al caso
-- base 1, pero si dabamos como entrada 0, obteníamos un stackoverflow. 
-- Si el caso base no se cumple, pasamos recursivamente a x-1 y usamos la función move para obtener la siguiente fila.
pascalN :: Int -> [Int]
pascalN x
  | x == 0 = [0]
  | x == 1 = [1]
  | otherwise = move (pascalN (x - 1))
move :: [Int] -> [Int]
move inLine = [1] ++ zipWith (+) inLine (tail inLine) ++ [1]
