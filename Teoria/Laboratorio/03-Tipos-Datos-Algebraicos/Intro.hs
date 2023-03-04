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
    tls = [(x,y,z) | z<-[1..10], y<-[1..z], x<-[1..y],x^2+y^2 == z^2, x + y + z == 24]

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
    factorial n = product' [1..n]

    product' :: (Num a) => [a] -> a 
    product' [] = 1
    product' (x:xs) = x * (product' xs)
    

    -- Recursión
    factorial' :: (Integral a) => a -> a
    factorial' 1 = 1
    factorial' n = n * (factorial' (n-1))

    {-
    Ejemplo
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
    Ejemplo
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

    -- EXPRESIONES CASE
    --- Alternativa al pattern matching

    contieneUno :: [Int] -> Bool
    contieneUno [] = False
    contieneUno (1:xs) = True
    contieneUno (x:xs) = contieneUno xs

    contieneUno' :: [Int] -> Bool
    contieneUno' [] = False
    contieneUno' (x:xs) = case x of
                            1 -> True
                            x -> contieneUno' xs

    
    
--- ### FUNCIONES DE ORDEN SUPERIOR ### 
    {-
    Las funciones de Haskell pueden tomar funciones como parámetros y 
    devolver funciones como resultado. Una función que hace ambas cosas 
    o alguna de ellas se llama función de orden superior.
    -}

    -- CURRIFICACIÓN
    suma3 :: Int -> Int
    suma3 = (+) 3

    suma' :: Int -> (Int -> (Int -> Int))
    suma' x y z = x + y + z

    -- FUNCIONES COMO PARAMETROS
    aplicarDoble :: (a->a) -> a -> a
    aplicarDoble f e = f (f e)

    -- Map
    {--
    map :: (a -> b) -> [a] -> [b]
    map _ [] = []
    map f (x:xs) = f x : map f xs
    --}
    duplicar :: [Int] -> [Int]
    duplicar xs = map (*2) xs  

    -- Filter
    {--
    filter :: (a -> Bool) -> [a] -> [a]
    filter _ [] = []
    filter p (x:xs)
      | p x       = x : filter p xs
      | otherwise = filter p xs
    --}
    menoresCinco :: [Int] -> [Int]
    menoresCinco xs = filter (<5) xs  

    -- Lambdas
    sumarDuplas :: (Num a) => [(a,a)] -> [a]
    sumarDuplas = map (\(a,b) -> a + b)

    -- Programación origami
    {-
    Volviendo a cuando tratábamos con la recursión, nos dimos cuenta 
    de que muchas funciones operaban con listas. Solíamos tener un caso base 
    que era la lista vacía. Debíamos usar un patrón x:xs y hacíamos alguna 
    operación con un solo elemento de la lista. Esto sugiere que es un 
    patrón muy común, así que unas cuantas funciones muy útiles fueron 
    creadas para encapsular este comportamiento. Estas funciones son llamadas 
    pliegues (o folds en ingles). Son una especie de función map, solo que reducen 
    la lista a un solo valor.

    Patron capturar

    fun :: [a] -> b
    fun [] = valor_base
    fun (x:xs) = f x (fun xs)

    -}

    prods' :: (Num a) => [a] -> a
    prods' [] = 1
    prods' (x:xs) = x * prods' xs
    -- foldl
    {-
    foldl :: (b->a->b) -> b -> [a] -> b
    foldl f z []     = z                  
    foldl f z (x:xs) = foldl f (f z x) xs
    -}
    prodsl :: (Num a) => [a] -> a
    prodsl = foldl (\acc x -> acc * x) 1
    {--
    prodsl [1,2,3]
    = foldl f 1 [1,2,3]
    = foldl f 1 [2,3]
    = foldl f 2 [3]
    = foldl f 6 []
    = 6
    -}
    -- foldr
    {-
    foldr :: (a->b->b) -> b -> [a] -> b
    foldr f z []     = z 
    foldr f z (x:xs) = f x (foldr f z xs) 
    -}
    prodsr :: (Num a) => [a] -> a
    prodsr = foldr (\x acc -> x * acc) 1
    {-
    prodsr [1,2,3]
    = foldr f 1 [1,2,3]
    = 1 * (foldr f 1 [2,3])
    =      (2 * (foldr f 1 [3]))
    =           (3 * (foldr f 1 []))
    =1 * (2 * (3*1 ))
    =6
    -}

   -- LIBRO
   -- ES: http://aprendehaskell.es/
   -- EN: http://learnyouahaskell.com/
    