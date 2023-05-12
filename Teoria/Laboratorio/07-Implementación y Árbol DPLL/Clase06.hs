
-- (p o q) y (-p o r o s) y (p) y (-p)
-- [[p,q],[-p,r,s],[p],[-p]]
-- (p = True) := [[p,q],[-p,r,s],[-p]] unit
-- (p = True) := [[-p,r,s],[-p]] elim
-- (p = True) := [[r,s],[]] red
-- NO HAY MODELO!! conflict

-- (p o q) y (-p o r o s) y (p) y (r)
-- [[p,q],[-p.r,s],[p],[r]]
-- (p = True) := [[p,q],[-p,r,s],[r]] unit
-- (p = True, r = True) := [[p,q],[-p,r,s]] unit
-- (p = True, r = True) := [[-p,r,s]] elim
-- (p = True, r = True) := [] elim (AUNQUE QUITAMOS UNA POR UNA, SE DEBE HACER EN UNA SOLA EJECUCION DE LA FUNCION)
--- MODELO = (p = True, r = True) success

-- (p o q) y (-p o r o s) y (p) y (-p) y (-r)
-- [[p,q],[-p,r,s],[p],[-p]]
-- (p = True) := [[p,q],[-p,r,s],[-p],[-r]] unit
-- (p = True, r = False) := [[p,q],[-p,r,s],[-p]] unit
-- (p = True, r = False) := [[-p,r,s],[-p]] elim (EN UNA SOLA EJECUCION DE LA FUNCION SE QUITAN TOFAS)
-- (p = True) := [[s],[]] red
-- NO HAY MODELO!! conflict

-- conflict (i, f) = elem [] f
-- success (i,f) ) f==[]
-- unit s@(i,f) = case (findUnitCl f) of
                        -- Nothing -> s
                        -- Just [l] -> ((l,True):i,filter (=[l) f)
--                  

-- dpll f = dpll' (DpllTree ([],f) Void Void)....