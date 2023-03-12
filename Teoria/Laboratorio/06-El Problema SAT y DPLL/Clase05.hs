module Clase05 where
{-

EJEMPLOS REGÑAS DPLL

-- Ejemplo unit

([], [[l],[p,q]])
-- ==>
([(l,True)],[[p,q]])

([], [[-l],[p,q],[l]])
-- ==>
([(l,False)],[[p,q],[l]]) --- NO SE PUEDE APLICAR UNIT, YA QUE -l ESTA EN EL MODELO


-- Ejemplo elim
([(l,True)],[[p,q],[l,r]])
-- ==>
([(l,True)],[[p,q]])


-- Ejemplo red
([(l,True)],[[p,q],[-l,r]])
-- ==>
([(l,True)],[[p,q],[r]])


-- Ejmeplo conflicto
([], [[-l],[p,q],[l]])
-- ==> UNIT
([(l,False)],[[p,q],[l]])
-- ==> RED
([(l,False)],[[p,q],[]])
--- ==> CONFLICT
-- formula NO satisfacible

--Ejemplo separación
([], [[p,q],[r,s]])
===> sep
(([(p,True)], [[p,q],[r,s]])  ,  ([(p,False)], [[p,q],[r,s]])
-}
--- DUDAS

{-
Supongamos que tenemos una lista y la función lo que hace es eliminar 
un elemento de esa lista y regresar la lista nueva sin el elemento. 
elimina :: a -> [a] -> [a]
elimina a xs = delete a xs 
(y aquí necesito regresar la lista sin el elemento pero no puedo ponerlo después del delete, 
eso como podría ser(porque según yo delete no regresa una lista)) 

-- recuerden que haskell al ser funcional no tieen estado, entonces funciones como delete
no modifican la variable xs, si no cran una nueva lista que seria xs sin el elemento
y te lo regresan


2: como podemos ir imprimiendo en una función?

No se puede hacer algo como un "console.log" en haskell, ya que este es un lenguaje funcional
para ver la evaluacion de una funcion pueden hacer cosas como las de abajo :)
saturacionN :: [Clausula] -> Int -> [Clausula]
saturacionN cs n
  | n == 0 = cs
  | otherwise = saturacionN  cs' (n-1)
   where cs' = sortBy (\e1 e2 -> compare (length e1) (length e2)) (resBin cs)

saturacionN cls 6


dpllN :: Estado -> Int -> Estado
dpllN e@(m,cls) n
| n == 0 = e
| otherwise dpllN e' (n-1)
    where e' = ...
-}

{-
EXTRA

Implementar un evaluador de formulas proposicionales
dado que:

eval :: Interpretacion -> Prop -> Bool

Tomando en cuenta las siguientes condiciones:
- Si una variable no esta en la inrepretcion regresr un error
- NO pueden transformar la formula a formas normales, debe evaluarse tal cual
  (aunque si pueden usar equivalencias en la evaluacion de las expresiones)
-}
