module Intro where

--Instalación de Haskell
    -- Web Haskell: https://www.haskell.org/
    -- GhCup para instalar: https://www.haskell.org/ghcup/

-- Qué es Haskell?
{-
    Haskell es un lenguaje de programación puramente funcional. 
    En los lenguajes imperativos obtenemos resultados dándole al 
    computador una secuencia de tareas que luego éste ejecutará. 
    Mientras las ejecuta, puede cambiar de estado.

    Con la programación puramente funcional no decimos al computador 
    lo que tiene que hacer, sino más bien, decimos como son las cosas.
    Expresamos la forma de las funciones.

    Si una función es llamada dos veces con los mismos parámetros, obtendremos 
    siempre el mismo resultado. A esto lo llamamos transparencia referencial

    - perezoso
    - tipificado estáticamente
    - inferencia de tipos
    GHC: compilador para haskell (glaskow haskell compiller)
-}

-- ##### TIPOS ####

    -- TIPOS
    -- Tipado estatico
    -- Inferencia de tipos
    -- Comienzan con masyúsculas
    -- Int, Integer, Float, Double, Bool, Char
    ej1 :: Bool
    ej4 :: Int
    ej1 = True; ej2 = 'a'; ej3 = "Hola"; ej4 = 2; ej5 = 2.0
    -- Tipo función
    fun1 :: Int -> Int
    fun1 a = a + 5
    
    
    -- VARIABLES DE TIPO
    -- Pueden ser cualquier tipo
    -- Tipos genericos
    -- Funciones polimorficas
    -- head?, fst?
    headFst :: [(a,b)] -> a
    headFst xs = fst (head xs) 

    -- CLASES DE TIPO
    -- Especie de "interfaz"
    {- Si un tipo es miembro de una clase de tipos, significa que ese tipo 
       soporta e implementa el comportamiento que define la clase de tipos. -}
    -- Eq, Ord, Shobcw, Enum, Bounded, Num, Integral
    eq :: (Eq abc) => abc -> abc -> Bool
    eq  = (==)
  -- eq a b = (==) a b

-- #### LISTAS Y TUPLAS ####

    -- LISTAS
    -- Homogeneas
    l1 = [1,2,3,4]; l2 = "Me gustas Haskell"
    -- (++), (!!), head, tail, last, ...
    l3 = "Ramon " ++ "Arenas"; v1 = l3 !! 6
    -- Rangos
    l4 = [1..20]
    -- Lista por comprensión
    l5 = [x | x <- [1..100], (mod x 2) == 0 ]
    -- Listas infinitas
    l6 = cycle [1,2,3,4]

    l100 = take 20 [x | x <- [1..], (mod x 2) == 0 ]

    -- TUPLAS
    -- Heterogeneas
    t1 = (1,"Soy un elemento de una dupla")
    -- Tamaño exacto (número de elementos)
    t2 = (1,2,'c'); t3 = (6,3,'a')
    l7 = [1,2,3]; l8 = [1,2,3,4]
    ls1 = [l7,l8] -- ls2 = [t2,t3]
    -- fst, snd...
    v2 = fst t1; v3 = snd t1
    
    {- 
    Ejercicio
    ¿Qué triángulo recto cuyos lados miden enteros menores o iguales que 10 tienen un 
    perímetro igual a 24?
    -}

--- ### FUNCIONES ###
    -- PATTERN MATCHING
    -- Ejemplo
    lucky :: (Integral a) => a -> String
    lucky 7 = "¡El siete de la suerte!"
    lucky x = "Lo siento, ¡no es tu día de suerte!"
    
    -- Ejemplo error orden
    sayMe :: (Integral a) => a -> String
    sayMe x = "No se ha agregado soporte para este número"
    sayMe 1 = "¡Uno!"
    sayMe 2 = "¡Dos!"
    sayMe 3 = "¡Tres!"
    sayMe 4 = "¡Cuatro!"

    -- Ejemplo error exhaustividad
    charName :: Char -> String
    charName 'a' = "Alberto"
    charName 'b' = "Braulio"
    charName x = "Aun no implementada"

    -- Patrones con listas
    len :: [a] -> Int
    len [] = 0
    len (x:xs) = 1 + (len xs)

    -- Patrones con duplas
    addVectors :: (Num a) => (a, a) -> (a, a) -> (a, a)
    addVectors a b = (fst a + fst b, snd a + snd b)

    addVectors' :: (Num a) => (a, a) -> (a, a) -> (a, a)
    addVectors' (x1, y1) (x2, y2) = (x1 + x2, y1 + y2)


    -- RECURSION
    -- Sin recursión
    factorial :: (Integral a) => a -> a
    factorial n = product [1..n]

    product' :: (Num a) => [a] -> a 
    product' [] = 1
    product' (x:xs) = x * (product' xs)
    

    -- Recursión
    factorial' :: (Integral a) => a -> a
    factorial' 1 = 1
    factorial' n = n * (factorial' (n-1))

{-
factorial 5
5 * factorial 4
    4 * factrial 3
        3 * factorial
        --- factorial 1 = 1
-}
    

    -- Recursión de cola
    factorialT :: (Integral a) => a -> a -> a
    factorialT 0 acc = acc
    factorialT n acc = factorialT (n-1) (n*acc)

    fact x = factorialT x 1

{-
factorial 5 1
factorial 4 5
factrial 3 20
factorial 2 60
factorial 1 120
factorial 0 120 = 120
-}
    

    -- IF VS GUARDAS
    -- Comprobar si alguna propiedad de una valor (o varios de ellos) es cierta o falsa.
    -- If
    isOld :: Int -> Bool
    isOld n = if n>60
              then True
              else False

    -- Guardas
    -- Grandes árboles if de manera mas clara
    -- Pattern matching sobre patroes, guardas sobre condición booleana
    
    imcTellIf :: (RealFloat a) => a -> String
    imcTellIf bmi = if bmi <= 18.5
                    then "Infrapeso"
                    else (if bmi <= 25.0
                         then "Normal"
                         else "NO conitnuare el ejemplo por que da flojera...")

    imcTell :: (RealFloat a) => a -> String
    imcTell bmi
      | bmi <= 18.5 = "Infrapeso"
      | bmi <= 25.0 = "Normal"
      | bmi <= 30.0 = "Sobrepeso"
      | otherwise   = "Obesidad"
    -- "otherwise" acepta cualquier condición, si no hay otherwise y no se
    -- acepta ninguna guardia se sigue al siguiente patron


    -- ASIGNACIONES LOCALES (WHERE VS LET)
    imcTell' :: (RealFloat a) => a -> a -> String
    imcTell' weight height
      | weight / height ^ 2 <= 18.5 = "Infrapeso"
      | weight / height ^ 2 <= 25.0 = "Normal"
      | weight / height ^ 2 <= 30.0 = "Sobrepeso"
      | otherwise                   = "Obesidad"
    
    -- Where
    imcTellW :: (RealFloat a) => a -> a -> String
    imcTellW weight height
      | bmi <= 18.5 = "Infrapeso"
      | bmi <= 25.0 = "Normal"
      | bmi <= 30.0 = "Sobrepeso"
      | otherwise   = "Obesidad"
      where bmi = weight/ height ^ 2
    
    -- Let
    --- No hay forma de hacer una asignación local que sea reconocida
    --- en todas las guardas con let
    imcTellL :: (RealFloat a) => a -> a -> String
    imcTellL weight height
      | let bmi = weight / height in bmi <= 18.5 = "Infrapeso"
      | let bmi = weight / height in bmi <= 25.0 = "Normal"
      | let bmi = weight / height in bmi <= 30.0 = "Sobrepeso"
      | otherwise   = "Obesidad"