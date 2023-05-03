module DPLL where

import Prop
import Data.List (nub, maximumBy)
import Data.Ord (comparing)
            
type Interpretacion = [( String , Bool ) ]
type Estado = ( Interpretacion , [ Clausula ])

conflict :: Estado -> Bool
conflict (_, clausulas) = [] `elem` clausulas

success :: Estado -> Bool
success (_, clausulas) = null clausulas

unit :: Estado -> Estado
unit (i, cs) = case findUnitClause cs of
                    Just l  -> (updateModel l i, filter (not . elem l) cs)
                    Nothing -> (i, cs)
    where
        findUnitClause :: [Clausula] -> Maybe Literal
        findUnitClause cs = case filter (\c -> length c == 1) cs of
                                []     -> Nothing
                                (c:_)  -> Just $ head c

        updateModel :: Literal -> Interpretacion -> Interpretacion
        updateModel l i = case l of
                            V s     -> ((s, True):i)
                            NotV s  -> ((s, False):i)

addAllUnitLiterals :: Estado -> Estado
addAllUnitLiterals (i, cs) = case findUnitClause cs of
                               Just l  -> addAllUnitLiterals (updateModel l i, filter (not . elem l) cs)
                               Nothing -> (i, cs)
    where
        findUnitClause :: [Clausula] -> Maybe Literal
        findUnitClause cs = case filter (\c -> length c == 1) cs of
                                []     -> Nothing
                                (c:_)  -> Just $ head c

        updateModel :: Literal -> Interpretacion -> Interpretacion
        updateModel l i = case l of
                            V s     -> ((s, True):i)
                            NotV s  -> ((s, False):i)

elim :: Estado -> Estado
elim (int, cls) = (int, filter (not . containsTrueLiteral int) cls)
    where
        containsTrueLiteral :: Interpretacion -> Clausula -> Bool
        containsTrueLiteral int cls = any (\l -> evalLiteral int l == True) cls
        evalLiteral :: Interpretacion -> Literal -> Bool
        evalLiteral int (V s) = lookup s int == Just True
        evalLiteral int (NotV s) = lookup s int == Just False

red :: Estado -> Estado
red (int, cls) = (int, map (eliminarNegacion int) cls)
    where
        eliminarNegacion :: Interpretacion -> Clausula -> Clausula
        eliminarNegacion int cls = filter (\l -> evalLiteral int l /= Just False) cls
        evalLiteral :: Interpretacion -> Literal -> Maybe Bool
        evalLiteral int (V s) = lookup s int
        evalLiteral int (NotV s) = case lookup s int of
                                        Just b -> Just (not b)
                                        Nothing -> Nothing

sep :: Literal -> Estado -> (Estado, Estado)
sep p (i, cs) = case p of
                  (V s) -> (((s, True):i, cs), ((s, False):i, cs))
                  (NotV s) -> (((s, True):i, cs), ((s, False):i, cs))

data ArbolDPLL = Node Estado ArbolDPLL | Branch Estado ArbolDPLL ArbolDPLL deriving (Eq, Show)

heuristicsLiteral :: [Clausula] -> Literal
heuristicsLiteral cs =
  let allLiterals = concat cs
      literalsCount = map (\l -> (l, length $ filter (elem l) cs)) allLiterals
  in fst $ maximumBy (comparing snd) literalsCount

dpll :: [Clausula] -> Interpretacion
dpll [] = []
dpll cls | conflict ([], cls) = []
         | otherwise =
            let (i, cs) = red (elim (addAllUnitLiterals ([], cls)))
            in if success (i, cs)
                then i
                else dpllAux (i, cs)

dpllAux :: Estado -> Interpretacion
dpllAux (i, []) = i -- Caso base: todas las cláusulas son verdaderas, devolvemos la interpretación
dpllAux (i, cls) =
    let l = head (head cls) -- Tomamos la primera literal de la primera cláusula
    -- let l = heuristicsLiteral cls -- Tomamos la literal con más ocurrencias
        (e1, e2) = sep l (i, cls) -- Separamos el estado en dos, tomando la primera literal como verdadera y falsa
    in case (success e1, success e2) of
        (True, _) -> dpllAux e1 -- Si e1 es satisfactorio, seguimos evaluando con e1
        (_, True) -> dpllAux e2 -- Si e2 es satisfactorio, seguimos evaluando con e2
        otherwise -> dpllAux (red (elim e1)) ++ dpllAux (red (elim e2)) -- Si ninguno es satisfactorio, evaluamos con ambos estados y concatenamos las interpretaciones resultantes
