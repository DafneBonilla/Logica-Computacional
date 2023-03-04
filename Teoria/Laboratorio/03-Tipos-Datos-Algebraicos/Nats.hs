--Módulo para definir los naturales
module Naturales where
    import Intro
    {-Construimos un nuevo data Nat, para representar los naturales
      Utilizamos deriving show para que se pueda mostrar en terminal-}
    data Nat = Cero
            | Succ Nat
            deriving (Show)

    --Convierte un número de nuestro tipo definido a Int de Haskell
    value :: Nat -> Int
    value Cero = 0
    value (Succ n) = 1 + (value n)

    --Convierte un Int de Haskell a nuestro tipo Nat
    toNat :: Int -> Nat
    toNat 0 = Cero
    toNat n
      | n > 0 = Succ (toNat (n-1))
      | otherwise = error "el número ingresado no es un natural" 

    
    sumaNat :: Nat -> Nat -> Nat
    sumaNat Cero n = n
    sumaNat (Succ n) m = Succ (sumaNat n m)
