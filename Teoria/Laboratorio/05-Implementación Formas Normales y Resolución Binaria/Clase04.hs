module Clase04 where
import Data.List
import Data.Maybe
 
data Prop = Var String | Cons Bool| Not Prop
          | And Prop Prop | Or Prop Prop
          | Impl Prop Prop | Syss Prop Prop
          deriving (Eq, Show)

type Literal = Prop
type Clausula= [Literal]

-- Ejemplo de como podríamos crear un nuevo data para literales.
-- Implica crear funciones para transformar de Prop a literal
data LiteralS = VarL String | VarNeg String

propToLit :: Prop -> LiteralS
propToLit (Var s) = VarL s
propToLit (Not (Var s)) = VarNeg s
propToLit _ = error "Formula NO es una literal"

-- Función clausulas,se completo fuera de la clase
clausulas :: Prop -> [Clausula]
clausulas = error "impl" 

getLiterals :: Prop -> Clausula
getLiterals (Or p q) = union (getLiterals p) (getLiterals q)
getLiterals p@(Var q) = [p]
getLiterals p@(Cons t)= [p]
getLiterals p@(Not q) = [p]
getLiterals p = error "Formula no soportada"

--- Ejemplo de lo que debía hacer clausulas
--- (p v q v r ) Y (r v s) Y (m v n)
-- [[p,q,r],[r,s],[m,n]]

-- Ejemplo de como se aplica la resolución binaria
--[p,q]  [r,-q]  ==> [p,r]
--[p,q] [p,-q] ==> [p]

-- Manera a patita (mas tardada)
-- Solo fue un ejemplo ilustrativo, esto NO ES FUNCIONAL
contieneComplemento :: Literal -> Clausula -> Bool
contieneComplemento x (ys) = elem (Not x) ys

-- Manera mas rapida
-- Utilizar find y listas por comprension
resolucion :: Clausula -> Clausula -> Clausula
resolucion c1 c2 = union (filter (\x-> x /= p) c1)  (filter (\x-> x /= p') c2)
            where Just (p, p') = find (\(x,y) -> sonComplemento x y) [(l1,l2) | l1<-c1, l2<-c2]

--- funciones auxiliares agregadas fuera de clase para que esto funcione
sonComplemento :: Literal -> Literal-> Bool
sonComplemento (Not p) q = p == q
sonComplemento p (Not q) = q == p
sonComplemento _ _= False

getComplements :: Clausula -> Clausula -> Maybe (Literal, Literal)
getComplements c1 c2 = find (\(x,y)-> sonComplemento x y) [(x,y) | x<-c1, y<-c2]

-- resolucionBin :: [Clausula] -> [Clausula]
-- resolucionBin cs = find [(c1,c2) | c1 <- cs, c2 <-cs, c1/=c2] --- SOLUCION INCOMPLETA
------ USAR FUNCION hayResolucion... y mas cosas
-- solucion resolucionBin
hayResolvente :: Clausula -> Clausula -> Bool
hayResolvente c1 c2 = error "No imp"

resolucionBin :: [Clausula] -> [Clausula]
resolucionBin xs = case res of
            Nothing -> xs
            Just (c1,c2) -> [c | c <- xs, c/=c1, c/=c2] ++ [(resolucion c1 c2)]
            where cands = [(c1,c2) | c1 <- xs, c2 <- xs, c1 /= c2]  
                  res = find (\(x,y) -> hayResolvente x y) cands

--- HINTS
{-
Usar Union, para simplificar todo
El orden en el que alacenan las clausulas IMPORTA (sortBy)
  -- ordenar las clausulas de menor a mayor numero de elementos
  -- (sortBy (\x y -> compare (lenth y) (length x)) clausulas)
-}

-- Ejemplo de como podria hacerse saturacion
saturacion :: [Clausula] -> Bool
saturacion cs
  | cs == cs' = True
  | elem [] cs = False
  | otherwise = saturacion cs'
  where cs' = resolucionBin cs

{- FNC vs FND
 Forma normal conjuntiva => Conjunciones de Clausulas (literales con OR)
 Forma normal disyuntiva => Disyunciones de literales con AND

 (p AND q) OR (s AND r)

 ======== EJERCICIO EXTRA =========
IMPLEMETAR LA FUNCION
fnd :: Prop -> Prop
fnd = error "Recibe una proposicon en fnn y la convierne a su fnd"

-}

--- Ejemplo de como sería fnn
fnn :: Prop -> Prop
fnn p = negs_remove $ morgan $ imp_remove p

negs_remove = error ""
morgan = error ""
imp_remove = error ""

--- SOLUCIÓN EXTRA
fnd :: Prop -> Prop
fnd p = fnd' $ fnn p

fnd' :: Prop -> Prop
fnd' prop@(And p q) = case (fnd' p, fnd' q) of
                     (Or r s, t) -> Or (fnd' (And r t)) (fnd' (And s t))
                     (r, Or s t) -> Or (fnd' (And r s)) (fnd' (And r t))
                     (r,s) -> prop
fnd' (Or p q) = Or (fnd' p) (fnd' q)
fnd' p = p