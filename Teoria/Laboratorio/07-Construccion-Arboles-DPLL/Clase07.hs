{-

--- [Cls] 
--- ([],[Cls]) estado inicial

conflict y success -- terminan el algoritmo

unit, elim, red -- modifican el estado
-- unit: modifica modelo y formula (depende de lo que hay en la formula)
-- elim y red: solo modifican la formula (dependen de lo que hay en el modelo)

separacion -- explora posibilidades 


--- [] , [[p,q,r],[-r],[p],[-p,q]] unit
-- [(p,True)] , [[p,q,r],[-p,q]] elim y red
-- [(p,True)] , [[q]]

--- cada transicion s -> s' = aplicar (red $ elim unit s = s')

 construir el arbol de s :
 si success s o conflict s = Node s Void -- caso base
 si trans s /= s Node s (construye arbol de trans s) (trans = red $ elim unit)
 y en otro caso construir Branch s (constrir el arbol resultado 1 de sep s) (constrir el arbol  resultado dos de sep s)

(OPCION MAS SENCILLA)
 explorar un arbol
Void -> ??? (tener un "acumulador" que guarde el estado que se tiene) y regresar ese estado
Node s (tree') -> explorar tree' actualizando el acumulador a s
Branch s (tree1) (tree2) -> explotrar tree1 pasando s al acumulador
                            si el resultado es vacio explorar tree2
                            si no regresar lo obtenido

(OPCION COMPLICADA)
 explorar un arbol
Void -> ??? (tener un "acumulador" que guarde el estado que se tiene) y regresar ese estado
Node s (tree') -> revisar si hay conflicto
                    SI HAY CONFLICTO
                    opcion 1: (pasar un estado con modelo vacio al acumulador y revisar subhijo)
                    opcion 2: (regresar directamente el estado con modelo vacio e interrumpor ejecucion)
                    NO HAY CONFLICTO
                    si hay succes regresar el modeo actual
                    si no hay succes pasar el estado al acumulador y explorar el sub arbol
Branch s (tree1) (tree2) -> explotrar tree1
                            si el resultado es vacio explorar tree2
                            si no regresar lo obtenido

IDEA IMPORTANTE DE ESTO
-Primero construir el arbol
-DEspues explorarlo buscando el modelo

ejemplo de construcción del arbol

f = [[duerme,¬duerme],[duerme,salta],[corre,¬duerme],[corre,salta]]
s0 = ( [], [[duerme,¬duerme],[duerme,salta],[corre,¬duerme],[corre,salta]])

no se puede aplicar unit, elim o red -> se aplica sep y se construye un branch
literal = ¬duerme
t0 = Branch s0 (t1l) (t1r)

se construyen recursivamente t1l y t1r con los estados s1l y s1r respectivamente
---------------------
s1l = ([("duerme",False)],[[duerme,¬duerme],[duerme,salta],[corre,¬duerme],[corre,salta]])
t1l = Node s1l t2l

s2l = ([("duerme",False)] , [[salta],[corre,salta]]) ::: se aplicaron las reglas desde s1l 
                                                         y se construye un Node
t2l = Node s2l t3l 

s3l = ([("duerme",False),("salta",True)],[]) ::: se aplicaron las reglas desde s2l 
                                                 y se construye un Node
t3l = Node s3l Void ::: habia success en s3l por lo tanto se crea una hoja (su hijo es void)

-----------------

s1r = ([("duerme",True)] , [[duerme,¬duerme],[duerme,salta],[corre,¬duerme],[corre,salta]])
t1r = Node s1r t2r  

s2r = ([("duerme",True)],[[corre],[corre,salta]]) ::: se aplicaron las reglas desde s1r 
                                                         y se construye un Node
t2r = Node s2r t3r 

s3r = ([("corre",True),("duerme",True)] , []) ::: se aplicaron las reglas desde s2r 
                                                         y se construye un Node
t3r = Node  Void ::: habia success en s3r por lo tanto se crea una hoja (su hijo es void)

Una aproximacion grafica del arbol sería asi:

( [], [[duerme,¬duerme],[duerme,salta],[corre,¬duerme],[corre,salta]])
   |                                             \
   |                                              \
   |                                               \
   |                                                \
   |                                                 \
   |                                                  \
([("duerme",False)],                               ([("duerme",True)] , 
 [[duerme,¬duerme],[duerme,salta],                 [[duerme,¬duerme],[duerme,salta],[corre,¬duerme],[corre,salta]])
 [corre,¬duerme],[corre,salta]])                         |
   |                                                     |
   |                                                     |
   |                                                     |
   |                                                     |
([("duerme",False)] ,                              ([("duerme",True)],
[[salta],[corre,salta]])                           [[corre],[corre,salta]])
   |                                                     |
   |                                                     |
   |                                                     |
   |                                                     |
([("duerme",False),("salta",True)],[])             ([("corre",True),("duerme",True)] , [])

Despues de construir el arbol habria que explorarlo para encontar un modelo en las hojas de caso success

PROBLEMA DE NUESTRO ALGORITMO

-- esta en como aplicamos la regla de separacion
-- nuestra heuristica para variable soempre va regresar la misma

imaginen que para una formula satisfacible aplicamos la regla de separacion con la literal p
-- ambas ramas de nuestro arbol llegamos a conflicto, eso significa que nuestra formula
   no era satisfacible?


    
-}

