/* Ejercicio 1 */

% Vemos si la cabeza de la lista es X.
elem(X,[X|_]). 
% De manera recursiva, vemos si X está en la cola de la lista.
elem(X,[_|M]) :- elem(X,M). 

/* Ejercicio 2 */

% Vemos si un elemento X de M está en la lista N usando elem. Si es así, entonces el predicado 
% devuelve <true>, de lo contrario devuelve <false>. Esta regla se ejecuta para todos los elemento de M.
intersect(M, N) :- elem(X, M), elem(X, N).

/* Ejercicio 3 */

% Vemos si X es la cabeza de la lista. Si se cumple, se devuelve la cola de la lista Y como NewL. 
delete(X, [X|L], L).
% Copiamos la cabeza de la lista Y a la nueva lista, y usamos recursivamente delete(X) para la 
% cola de la lista L, obteniendo la cola de la nueva lista NewL. Unimos la nueva cabeza de la lista 
% Y con la cola de la nueva lista NewL para obtener la lista completa final.
delete(X, [Y|L], [Y|NewL]) :- delete(X, L, NewL).

/* Ejercicio 4 */

% Algoritmo Hao Wang
% Regla 1
wang(G,D) :- intersect(G,D),!. % Revisa si existe un elemento en común y para al encontrar al menos uno.

% Regla 2
wang(G,D) :- elem(not(A),G),      % Revisa si la negación de A pertenece a G
             delete(not(A),G,NG), % Construye una lista NG que es igual a G sin la negación de A
             wang(NG,[A|D]),!.    % Revisa que NG deriva [A|D] sea válida.

% Regla 3
wang(G,D) :- elem(not(A),D),      % Revisa si la negación de A pertenece a D
             delete(not(A),D,ND), % Construye una lista ND igual a D sin la negaicón de A
             wang([A|G],ND),!.    % Revisa que [A|G] deriva ND sea válida

% Regla 4
wang(G,D) :- elem(and(A,B), G),     % Revisa si hay una conjunción en G
             delete(and(A,B),G,NG), % Construye una lista NG igual a G sin dicha conjunción
             wang([A,B|NG],D),!.    % Revisa si es válido que la lista con A y B separados y los elementos de NG deriva D.

% Regla 5
wang(G,D) :- elem(or(A,B), D),       % Revisa si hay una disyunción en D
             delete(or(A,B), D, ND), % Construye una lista ND igual a D sin dicha disyunción
             wang(G,[A,B|ND]),!.     % Revisa si G deriva a la lista que tiene a A y B separados y los elementos de ND.

% Regla 6
wang(G,D) :- elem(or(A,B),G),        % Revisa si hay una disyunción en G 
             delete(or(A,B),G,NG),   % Construye una lista NG igual a G sin dicha disyunción
             wang([A|NG],D),         % Revisa si es válido que la lista con A y los elementos de NG deriva a D
             wang([B|NG],D),!.       % Revisa si es válido que la lista con B y los elementos de NG deriva a D

% Regla 7
wang(G,D) :- elem(and(A,B), D),         % Revisa si hay una conjunción en D
             delete(and(A,B), D, ND),   % Construye una lista ND igual a D sin dicha conjunción
             wang(G,[A|ND]),            % Revisa si G deriva a la lista con A y los elementos de ND
             wang(G,[B|ND]),!.          % Revisa si G deriva a la lista con B y los elementos de ND

/* Ejercicio 5 */

valid(F) :- wang([],[F]).

% Casos a probar:
% valid(or(not(p),p)). <- esto es p v ¬p
% valid(or(not(or(a,b)),or(a,b))). <- esto es (a v b) -> (a v b) lo que es ¬(a v b) v (a v b)
% valid(and(or(and(a,not(b)),or(b,not(a))),or(and(not(b),a),or(not(a),b)))). <- esto es (a -> b) <-> (¬b -> ¬a) lo que es (¬a v b) <-> (b v ¬a)
                                                                            %   que a su vez es [(¬a v b) -> (b v ¬a)] ^ [(b v ¬a) -> (¬a v b)]
                                                                            %   que es [¬(¬a v b) v (b v ¬a)] ^ [¬(b v ¬a) v (¬a v b)]
                                                                            %   que es [(a ^ ¬b) v (b v ¬a)] ^ [(¬b ^ a) v (¬a v b)]