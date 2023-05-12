module Prop where


data Prop = Var String | Cons Bool| Not Prop
          | And Prop Prop | Or Prop Prop
          | Impl Prop Prop | Syss Prop Prop
          deriving (Eq)

fnn :: Prop -> Prop
fnn = error "Implementar"

fnc :: Prop -> Prop
fnc = error "Implementar"

{- NOTAS LAB 03

EJEMPLOS FORMA NORMAL CONJUNTIVA
(-l ∨ r ∨ q) ∧ (q ∨ r) ∧ (t ∨ s ∨ t)

EJEMPLO DE APLICACIÓN RESOLUCIÓN BINARIA
(p ∨ q) ∧ (-p ∨ r)
 q ∧ r

GENERACIÓN DE CLAUSULAS VACIAS
p ∧ -p
[]   

EXPLICACIÓN DE PRECEDENCIA Y ASOCIATIVIDAD
--- 4 + 3 * 2 ==> 4 + (3*2)
--- 4 * 3 * 2 ==> (4 * 2) * 3
--- p-> q -> r ==> p -> (q -> r)
--- q ∧ p ∧ r ==> (q ∧ p) ∧ r ==> And (And (Var "q") (Var "p")) (Var "r")

HINTS PRACTICA
--- fnn ....
--- fnn (Impl p q) = Or ((fnn (Not p))) (fnn q)

--- fnc :: ...
--- fnc q = case (fnn q) of
--            (And q r) -> And (fnc q) (fnc r)
--            (Or (And k q) r)  -> And (Or (fnc r) (fnc k)) (Or (fnc r) (fnc q))
--            (Or q (And k r)) -> ....
--            (Or q (Or p r)) -> Or (Or q (Or p r)) 
--             a -> a

-}
