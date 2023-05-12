% EJERCICIOS DE LISTAS
%concatenacion
concat([],L,L).
concat([X|L1],L2,[X|L3]) :- concat(L1,L2,L3).
%concat (x:xs) ys = x:(concat xs ys)

%inversa
inversa(L1,L2) :- inversa_aux(L1,L2,[]).

inversa_aux([],L2,L2).
inversa_aux([X|L1],L2,L3) :- inversa_aux(L1,L2,[X|L3]).

/*
inversa([1,2,3],X):-
inversa_aux([1,2,3],X,[]):-
inversa_aux([2,3],X,[1]):-
inversa_aux([3],X,[2,1]):-
inversa_aux([],X,[3,2,1])
inversa_aux([],[3,2,1],[3,2,1])
*/

%palindromo
palindromo(L):-inversa(L,L).

%ultimo
ultimo_1(X,L):-inversa(L,[X|_]).

ultimo_2(X,[X]):-!.
ultimo_2(X,[_|L]):-ultimo_2(X,L).

ultimo_3(X,L):-concat(_,[X],L).

% (p, -p) |- []
% p |- p

% EJEMPLO ALGORITMO HAO WANG
/*
"If the Russians get ahead of the Americans in the arms race, they will
 take over the world. If the Russians announce that they are cutting their
 arms budget, Congress will cut the American arms budget. If the
 Americans cut their arms budget, but the Russians do not cut theirs, the
 Russians will get ahead of the Americans in the arms race. The Russians
 are devious and will announce that they have cut their arms budget
 in any case. Either the SALT talks will fail or the Russians will cut
 their arms budget.

 If the SALT talks fail, will the Russians take over the world?
 If the SALT talks don't fail, will the Russians take over the world?"


 TRADUCCIÓN A VARIABLES
a: "Russians get ahead of the Americans in the arms race"
b: "Russians announce they are cutting their arms budget"
c: "Americans cut their arms budget"
d: "Russians cut their arms budget"
e: "SALT fails"
f: "Russians take over the world"

PREMISAS
P1: a -> f === (-a v f)
P2: b -> c === (-b v c)
P3: (c & -d) -> a === -(c & -d) v a
P4: b
P5: e XOR d === (e v d) & -(e & d)

POSIBLES CONCLUSIONES
C1: e -> f === (-e v f)
C2: -e -> f === (e v f)

[(-a v f) , (-b v c), (-(c & -d) v a), b, ((e v d) & -(e & d))] => [(-e v f)]
[(-a v f) , (-b v c), (-(c & -d) v a), b, (e v d) , -(e & d)]   => [-e , f]
[(-a v f) , (-b v c), (-(c & -d) v a), b, (e v d), e]           => [f, (e & d)]

[(-a v f) , (-b v c), (-(c & -d) v a), b, (e v d), e]           => [f, e]  CORRECT!!
[(-a v f) , (-b v c), (-(c & -d) v a), b, (e v d), e]           => [f, d]

[(-a v f) , (-b v c), (-(c & -d) v a), b, (e v d), e]           => [f, d]
[-a, (-b v c), (-(c & -d) v a), b, (e v d), e]                  => [f, d]
[f , (-b v c), (-(c & -d) v a), b, (e v d), e]                  => [f, d] CORRECT!!

[-a, (-b v c), (-(c & -d) v a), b, (e v d), e]                  => [f, d]
[(-b v c), (-(c & -d) v a), b, (e v d), e]                      => [f, d, a]

[c, (-(c & -d) v a), b, (e v d), e]                             => [f, d, a]
[-b, (-(c & -d) v a), b, (e v d), e]                            => [f, d, a]
[(-(c & -d) v a), b, (e v d), e]                                => [f, d, a, b] CORRECT!!

[c, (-(c & -d) v a), b, (e v d), e]                             => [f, d, a]
[c, -(c & -d), b, (e v d), e]                                   => [f, d, a]
[c, a, b, (e v d), e]                                           => [f, d, a] CORRECT!

[c, -(c & -d), b, (e v d), e]                                   => [f, d, a]
[c, b, (e v d), e]                                              => [f, d, a, (c & -d)]

[c, b, (e v d), e]                                              => [f, d, a, -d]
[c, b, (e v d), e]                                              => [f, d, a, c] CORRECT!!

[c, b, (e v d), e]                                              => [f, d, a, -d]
[c, b, (e v d), e, d]                                           => [f, d, a] CORRECT!!


PROLOG  
PREMISAS
P1: or(neg(a),f)
P2: or(neg(b),c)
P3: or(neg(and(c,neg(d))),a)
P4: b
P5: and(or(e,d),neg(and(e,d)))

[or(neg(a),f) , or(neg(b),c) , or(neg(and(c,neg(d))),a), b, and(or(e,d),neg(and(e,d)))]

POSIBLES CONCLUSIONES
C1: or(neg(e),f)
C2: or(e,f)

creditos ejercicio
*/

% AYUDA PRACTICA HAO WANG
wang(G,D):-intersect(G,D),!.

wang(G,D):-elem(neg(A),G),
           delete(neg(A),G,NG),
           wang(NG,[A|D]),!.

wang(G,D):-elem(neg(A),D),
           delete(neg(A),D,ND),
           wang([A|G],ND),!.

%SOLUCION EXTRA
equiv(imp(A1,A2),or(neg(B1),B2)):-equiv(A1,B1),
                                  equiv(A2,B2).

equiv(syss(A1,A2),and(P1,P2)):-equiv(imp(A1,A2),P1),equiv(imp(A2,A1),P2).

equiv(and(A1,A2),and(B1,B2)):-equiv(A1,B1),
                              equiv(A2,B2).

equiv(or(A1,A2),or(B1,B2)):-equiv(A1,B1),
                            equiv(A2,B2).

equiv(neg(A),neg(B)):-equiv(A,B).

equiv(P,P):-atomic(P).