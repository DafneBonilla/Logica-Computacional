% Modelo funcional de Prolog
% Desde el punto de vista funcional, y de una manera genérica, 
% la diferencia entre el modelo de una «máquina procedimental» y el de una 
% «máquina lógica», a la primera hay que darle el algoritmo para resolver el problema
% (algoritmo y datos), a la segunda sólo hay que especificarle el problema (reglas y 
% datos-hechos). El lenguaje de especificación está basado en la lógica de predicados.

% La programación lógica implica un «estilo» de programación radicalmente distinto al 
% de la programación «tradicional» (procedimental, o imperativa). Se suele advertir que a 
% una persona que ya tenga alguna experiencia en programación le resulta más difícil 
% captar este estilo que a otra que carezca de ella. No existen sentencias de bucle 
% («repeat» , «while» , «for» ), ni sentencias «if...then...» ni «case» , ni siquiera 
% sentencias de asignación. 

% Como elementos nuevos, no presentes en los lenguajes tradicionales, 
% se dispone de la posibilidad de
% - declarar propiedades de objetos o individuos y relaciones entre ellos;
% - escribir reglas para definir nuevas propiedades o relaciones generales en 
%   función de otras ya declaradas o definidas
% - hacer consultas para comprobar si objetos o individuos concretos tienen ciertas 
%   propiedades o están en determinada relación, o cuáles de ellos tienen esas propiedades 
%   o están en esa relación

% Las categorías sintácticas principales en Prolog son los términos, los predicados, 
% las reglas y las consultas. Veamos (informalmente) su sintaxis y, paralelamente, 
% la semántica asociada.

% TERMINOS
% Semánticamente, un término representa a un objeto o a un individuo del universo del discurso.

% Terminos simples o átomos
% Los términos básicos son las constantes y las variables. 
% Una constante representa a un objeto o individuo determinado, 
% y una variable representa a uno genérico.
% Las variables deben empezar con una letra mayúscula o con el símbolo «_»
% las constantes pueden ser
% - constantes numéricas, como, por ejemplo, 2, -235, +3.14159,
% - constantes simbólicas, como, por ejemplo, x, pepe, ejemplo_de_constante, ’2’
%   (deben empezar con una letra minúscula, o ir entre apóstrofos.)
% Las constantes y las variables son términos simples (o átomos).
% 
% Términos estructurados o estructuras
% funciones y las listas

% Funciones
% Las funciones constan de un nombre de función y de uno o varios argumentos. 
% El número de argumentos es el grado de la función. 
% El nombre de función es una cadena alfanumérica con el mismo convenio que las constantes 
% (empezar por letra minúscula). A continuación se escriben los argumentos, 
% separados por comas y entre paréntesis. Por ejemplo
% - padre_de(pepe).- representa a un objeto que es el padre de pepe
%   (notese que pepe es una constante, si fuera una variable no representaria nada)
% - ordenador(superclon, ’i686-600’, ’Linux’, 2000).- representa un objeto ordenador,
%   cuyas caracteristicas estan especificadas por su atributos

% Listas
% Una lista es una secuencia ordenada de términos. Por ejemplo, [A1, A2, A3] es una lista 
% de variables, y [a1, a2, a3] una lista de constantes. La lista puede ser vacía []. 
% Si no es vacía, se puede considerar formada por una cabeza y una cola. Funcion de
% formación de listas cons(). cons(a1, cons(a2, cons(a3,[])))

% En lugar de «cons» (denominación típica no de Prolog, sino de LISP) se suele utilizar
% un punto [a1,a2,a3] = .(a1,.(a2,.(a3,[])))

% Aún más utilizado es el símbolo «|» con notación infija, es decir, una lista, en general,
% es o bien [] (lista vacía) o bien [C|L], donde C es la cabeza (un elemento o 
% una lista de elementos) y L la cola (otra lista)
% - [a1,a2,a3] = [a1|L], con L = [a2,a3]
% - [a1,a2,a3] = [a1,a2|L], con L = [a3]
% - [a1,a2,a3] = [a1,a2,a3|L], con L = []

% PREDICADOS Y LITERALES
% Un predicado aplicado a un objeto representa una propiedad de ese objeto, y puede 
% evaluarse como «verdadero» o «falso» . Así <<blanco(X)>> expresa la propiedad de que 
% el objeto X tiene el color blanco. Mientras X (que es una variable) no tome un valor concreto 
% el predicado no será ni verdadero ni falso. Al tomar X un valor, por ejemplo, X=nieve, 
% el predicado se aplica ya a un objeto concreto, y podemos decir que blanco(nieve) es verdadero;
% si X toma el valor carbón, podemos decir que blanco(carbón) es falso.
% 
% Si el predicado tiene más de un argumento, entonces representa una relación entre los objetos
% correspondientes a esos argumentos, <<padre(X,Y)>> representa una relación entre los individuos 
% X e Y. Y será verdadero si X es padre de Y.

% La sintaxis es la misma que la de las funciones, pero obsérvese que la semántica es totalmente distinta
% las funciones representan objetos (o individuos), y por tanto nunca pueden ser «verdaderas» 
% ni «falsas» .

% Un literal es o bien un predicado (literal positivo) o bien la negación de un predicado 
% (literal negativo). La negación se expresa anteponiendo los caracteres «not» al nombre del
% predicado, <<not(padre(X,Y))>> es verdadero si padre(X,Y) es falso, y viceversa.


% HECHOS
% Un hecho es un predicado que no contiene ninguna variable entre sus argumentos. Por ejemplo
% - blanco(nieve).  
% - padre(juan, luis).  
% - padre(juan, padre(eva)).
% (Este último hecho puede interpretarse como que Juan es el padre del individuo que 
% es padre de Eva. El símbolo «padre» , aunque se repite, representa cosas distintas en un caso 
% y en otro, en su primera aparición por la izquierda es un nombre de un predicado con 
% dos argumentos, y en la segunda es un nombre de función con un argumento).

% REGLAS
% Una regla sirve para representar conocimiento que en lenguaje natural se expresa mediante 
% una sentencia condicional. Por ejemplo, si en lenguaje natural decimos 
% «si X es padre de Y entonces Y es hijo de X» , en Prolog escribiremos
% - hijo(Y,X) :- padre(X,Y).
% El símbolo «:-» significa «si» , y la traducción directa al lenguaje natural de la regla es 
% «Y es hijo de X si X es padre de Y» 

% En general, una regla tiene una «cabeza» y un «cuerpo» . La cabeza es un predicado, 
% y el cuerpo una conjunción de literales; para indicar la conjunción se utiliza una 
% coma separando a los predicados del cuerpo, una definición de «abuelo» es
% - abuelo(X,Y) :- padre(X,Z),padre(Z,Y).
% Pero esta definición estaría incompleta, sólo cubre los abuelos paternos. 
% Podemos completarla añadiendo otra regla
% - abuelo(X,Y) :- padre(X,Z),madre(Z,Y).
% Escribir dos o más reglas para definir un predicado es la manera normal de expresar en 
% Prolog lo que en lógica sería una disyunción. En este caso, «X es abuelo de Y si... o 
% bien si...» . También puede expresarse explícitamente la disyunción mediante «;»
% - abuelo(X,Y) :- padre(X,Z),(padre(Z,Y);madre(Z,Y)).
% pero normalmente se prefiere la versión en dos reglas por su mayor claridad.

% CONSULTAS
% Una consulta se escribe como un predicado o como una conjunción de predicados. 
% Si la consulta no contiene variables entonces la máquina responde «YES» o «NO» según que 
% el predicado o la conjunción sean verdaderos o no. Si contiene variables, responde con el 
% valor o los valores para los cuales se hace verdadero.

% EJEMPLOS
% Arbol genealogico
%hermanos
padre(ramon,yo).
padre(ramon,beto).
padre(ramon,rodrigo).
padre(ramon,diego).
% abuelo materno
padre(salvador_1,guille_2).
padre(salvador_1,salvador_2).
padre(salvador_1,martin).
padre(salvador_1,juan).
%abuelo paterno
padre(pepe,ramon).
padre(pepe,luis).
padre(pepe,mary).
%primos maternos
padre(salvador_2,sofia).
padre(juan,daniel).
padre(martin,renata).
%primos paternos
padre(luis,braulio).

%madres
%hermanos
madre(guille_2,yo).
madre(guille_2,beto).
madre(guille_2,rodrigo).
madre(guille_2,diego).
%abuelo maternos
madre(guille_1,guille_2).
madre(guille_1,salvador_2).
madre(guille_1,martin).
madre(guille_1,juan).
%abuela paterna
madre(luisa,ramon).
madre(luisa,luis).
madre(luisa,mary).

%relaciones complejas
progenitor(X,Y) :- madre(X,Y).
progenitor(X,Y) :- padre(X,Y).

abuelo(X,Z) :- padre(X,Y),progenitor(Y,Z).
abuela(X,Z) :- madre(X,Y),progenitor(Y,Z).

hermano(X,Y):- padre(P1,X),padre(P2,Y),P1=P2,
               madre(M1,X),madre(M2,Y),M1=M2,
               not(X=Y).

% Factorial
factorial(0,1).
factorial(N,F):- N>0, A is N-1, factorial(A,B), F is N*B.





