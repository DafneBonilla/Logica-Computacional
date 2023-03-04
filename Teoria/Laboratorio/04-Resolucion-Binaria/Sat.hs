module Sat where

import Prop

type Literal = Prop
type Clausula = [Literal]

clausulas :: Prop -> [Clausula]
clausulas = error "Implementar"

resolucion :: Clausula -> Clausula -> Clausula
resolucion = error "Implementar"

hayResolvente :: Clausula -> Clausula -> Bool
hayResolvente = error "Implementar"

saturacion :: Prop -> Bool
saturacion = error "Implementar"

--- saturacion p = 
--    |contieneEmp p' = False
--    |hayResolvente p' = saturacion (res p')
--    |otherwise = True
--    where p' =clausulas $ fnc p

--- NOTA hayResolvente y res solo aplica entre dos clausulas
-- deben usarlas para crear la funcion que aplica entre todas 
-- las clausulas del conjunto p'