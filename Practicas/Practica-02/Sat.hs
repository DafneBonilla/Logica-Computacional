module Sat where

import Prop
import Data.List (nub)

type Literal = Prop 
type Clausula = [Literal]

clausulas :: Prop -> [Clausula]

clausulas (And p q) = clausulas p ++ clausulas q
clausulas p = [nub (literales p)]

literales :: Literal -> Clausula
literales (And p q) = literales p ++ literales q
literales p = [p]

resolucion :: Clausula -> Clausula -> Clausula

resolucion clause1 clause2 =
    let
        resolvente = [l | l <- clause1, notElem (neg l) clause2]
                    ++ [l | l <- clause2, notElem (neg l) clause1]
    in
        resolvente

hayResolvente :: Clausula -> Clausula -> Bool

hayResolvente clause1 clause2 = not (null resolvent)
    where
        resolvent = [l | l <- clause1, neg l `elem` clause2]
                    ++ [l | l <- clause2, neg l `elem` clause1]

saturacion :: Prop -> Bool
saturacion formula =
    let
        clauses = fnc formula
        saturated = saturar clauses clauses
    in
        elem [] saturated

saturar :: [Clausula] -> [Clausula] -> [Clausula]
saturar old new =
    let
        resolvents = [resolucion c1 c2 | c1 <- old, c2 <- new, hayResolvente c1 c2]
        derived = nub (resolvents ++ old ++ new)
    in
        if length new == length derived
            then derived
            else saturar new derived
