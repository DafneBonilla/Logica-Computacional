module Mascota where

data Mascota = Mascota {
                        nombre :: Name,
                        edad :: Int,
                        especie :: Especie,
                        color :: Color
                        }

-- Ejemplo de por que se usan los records
data Mascota2 = Mascota2 Name Int Especie Color

-- para obetner el color
getColor :: Mascota2 -> Color
getColor (Mascota2 _ _ _ c) = c

--- se tendrian que crear funciones similares para cada atributo, los records nos ahorran eso

instance Show Mascota where
    show m = "Hola soy " ++ (show $ nombre m) ++   " y soy un " ++ (show $ especie m)

instance Eq Mascota where -- == , /=
    (==) m n = especie m == especie n && color m == color n

data Especie = Gato | Perro | Hamster deriving (Show,Eq)
data Color = Cafe | Negro | Blanco | Manchas deriving (Show,Eq) 
type Name = String


getNombre :: Mascota -> Name
getNombre = nombre