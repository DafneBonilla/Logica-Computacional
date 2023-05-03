% Ejercicios Básicos:

% 1. Horóscopo

% Construimos la base de conocimiento
horoscopo(aries, 21, 3, 19, 4).
horoscopo(tauro, 20, 4, 20, 5).
horoscopo(geminis, 21, 5, 20, 6).
horoscopo(cancer, 21, 6, 22, 7).
horoscopo(leo, 23, 7, 22, 8).
horoscopo(virgo, 23, 8, 22, 9).
horoscopo(libra, 23, 9, 22, 10).
horoscopo(escorpio, 23, 10, 21, 11).
horoscopo(sagitario, 22, 11, 21, 12).
horoscopo(capricornio, 22, 12, 19, 1).
horoscopo(acuario, 20, 1, 18, 2).
horoscopo(piscis, 19, 2, 20, 3).

% Definimos una fecha válida
fecha(Dia, Mes) :-
    Mes >= 1,
    Mes =< 12,
    DiasEnMes = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31],
    MesMenos is Mes - 1,
    nth0(MesMenos, DiasEnMes, Dias),
    Dia >= 1,
    Dia =< Dias.

% Construimos la función signo
signo(Dia, Mes, Signo) :-
    fecha(Dia, Mes),
    horoscopo(Signo, DiaInicio, MesInicio, DiaFin, MesFin),
    ( (Mes = MesInicio, Dia >= DiaInicio, Dia =< 31)
    ; (Mes = MesFin, Dia =< DiaFin, Dia >= 1)
    ; (Mes > MesInicio, Mes < MesFin) ).

% 2. Longitud de una lista

% Caso base: La longitud de una lista vacía es cero.
longitud([], 0).
% Caso recursivo: La longitud de una lista no vacía es uno más la longitud de su cola.
longitud([_|T], N) :-      
    longitud(T, N1),
    N is N1 + 1.

% Árbol Genealógico:

% 1. Hechos
hombre("Homer Simpson").
hombre("Bart Simpson").
hombre("Abraham J. Simpson").
hombre("Clancy Bouvier").
hombre("Herbert Powel").

mujer("Marge Simpson").
mujer("Jacqueline Bouvier").
mujer("???").
mujer("Edwina").
mujer("Mona Simpson").
mujer("Patty Bouvier").
mujer("Selma Bouvier").
mujer("Abbie").
mujer("Ling").
mujer("Lisa Simpson").
mujer("Maggie Simpson").

progenitor("Homer Simpson", "Bart Simpson").
progenitor("Homer Simpson", "Maggie Simpson").
progenitor("Homer Simpson", "Lisa Simpson").
progenitor("Marge Simpson", "Bart Simpson").
progenitor("Marge Simpson", "Maggie Simpson").
progenitor("Marge Simpson", "Lisa Simpson").
progenitor("Jacqueline Bouvier", "Patty Bouvier").
progenitor("Jacqueline Bouvier", "Selma Bouvier").
progenitor("Jacqueline Bouvier", "Marge Simpson").
progenitor("Clancy Bouvier", "Patty Bouvier").
progenitor("Clancy Bouvier", "Selma Bouvier").
progenitor("Clancy Bouvier", "Marge Simpson").
progenitor("Abraham J. Simpson", "Herbert Powel").
progenitor("???", "Herbert Powel").
progenitor("Abraham J. Simpson", "Abbie").
progenitor("Edwina", "Abbie").
progenitor("Abraham J. Simpson", "Homer Simpson").
progenitor("Mona Simpson", "Homer Simpson").
progenitor("Selma Bouvier", "Ling").

pareja("Homer Simpson", "Marge Simpson").
pareja("Marge Simpson", "Homer Simpson").
pareja("Jacqueline Bouvier", "Clancy Bouvier").
pareja("Clancy Bouvier", "Jacqueline Bouvier").

% 1. Reglas
padre(X,Y) :-
    progenitor(Y,X),
    hombre(Y).

madre(X,Y) :-
    progenitor(Y,X),
    mujer(Y).

hermanos(X, Y) :-
    progenitor(Z, X),
    !,
    progenitor(Z, Y),
    X \= Y.

hermano(X, Y) :-
    progenitor(Z, X),
    !,
    progenitor(Z, Y),
    X \= Y,
    hombre(Y).

hermana(X, Y) :-
    progenitor(Z, X),
    !,
    progenitor(Z, Y),
    X \= Y,
    mujer(Y).

esposo(X, Y) :-
    pareja(X, Y),
    hombre(Y).

esposa(X, Y) :-
    pareja(X, Y),
    mujer(Y).

suegro(X, Y) :-
    pareja(X, Z),
    padre(Z, Y).

suegra(X, Y) :-
    pareja(X, Z),
    madre(Z, Y).

cuniados(X, Y) :-
    (pareja(X, Z), hermanos(Z, Y));
    (hermanos(X, Z), pareja(Z, Y)).

cuniado(X, Y) :-
    (pareja(X, Z), hermanos(Z, Y), hombre(Y));
    (hermanos(X, Z), pareja(Z, Y), hombre(Y)).

cuniada(X, Y) :-
    (pareja(X, Z), hermanos(Z, Y), mujer(Y));
    (hermanos(X, Z), pareja(Z, Y), mujer(Y)).

abuelo(X, Y) :-
    padre(X, Z),
    padre(Z, Y);
    madre(X, Z),
    padre(Z, Y).

abuela(X, Y) :-
    madre(X, Z),
    madre(Z, Y);
    padre(X, Z),
    madre(Z, Y).

nieto(X, Y) :-
    progenitor(X, Z),
    progenitor(Z, Y),
    hombre(Y).

nieta(X, Y) :-
    progenitor(X, Z),
    progenitor(Z, Y),
    mujer(Y).

tio(X, Y) :-
    (madre(X, Z), hermano(Z, Y));
    (padre(X, Z), hermano(Z, Y)).

tia(X, Y) :-
    ((madre(X, Z), hermana(Z, Y));
    (padre(X, Z), hermana(Z, Y))).

primo(X, Y) :-
    hombre(Y),
    ((madre(X, Z), hermanos(Z, H), progenitor(H, Y));
    (padre(X, Z), hermanos(Z, H), progenitor(H, Y))).

prima(X, Y) :-
    mujer(Y),
    ((madre(X, Z), hermanos(Z, H), progenitor(H, Y));
    (padre(X, Z), hermanos(Z, H), progenitor(H, Y))).