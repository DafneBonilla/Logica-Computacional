--Módulo donde definimos nuestras propias listas
module List where

    {-Creamos nuestro data List
      Los definimos como la lista vacia "Nil"
      Y como una lista de tipo a Cons un elemento de tipo a
    -} 
    data List a = Nil
              | Cons a (List a) 
              deriving (Show,Eq)

   -- Calcula la longitud de un data List
    lengthL :: List a -> Int
    lengthL Nil = 0
    lengthL (Cons x xs) = 1 + lengthL xs
    -- (x:xs) == (Cons x xs) Podemos ver que son similares a las listas de Haskell

    reverseL :: List a -> List a
    reverseL Nil = Nil
    reverseL (Cons x xs) = concatL (reverseL xs) (Cons x Nil) -- Cons xs x
    -- reverse (x:xs) = (reverse xs) ++ [x]

    concatL :: List a -> List a -> List a
    concatL Nil xs = xs
    concatL (Cons x xs) ys = (Cons x (concatL xs ys))
    --- concat (x:xs) ys = x:(xs ++ ys)
    --- xs= [1,2,3] ys= [4,5]