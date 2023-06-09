Module Props .

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint map {A B : Type} (F : A -> B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: l' => F x :: map F l'
  end.

(*FixPoint nos indica que esta es una función recursiva, por lo que tendremos:
  Caso Base: La lista es vacía => False
  Recursión: y :: l' descompone la lista en la cabeza y y la cola l'. Verifica-
  mos si el elemento buscado x es igual a la cabeza de la lista y. In x l' es
  una llamada recursiva a la función In para verificar si el elemento está pre-
  sente en la cola de la lista l'. Si el elemento está presente => True.*)
Fixpoint In {A : Type} (x : A) (l : list A) : Prop
  := match l with
  | [] => False
  | y :: l' => x = y \/ In x l'
  end.

(*Example indica que estamos definiendo un ejemplo que queremos demostrar, por 
  lo que tendremos:
  - simpl, que simplifica la expresión [1; 2; 3; 4; 5] eliminando cualquier ope-
  ración innecesaria.
  - right se utiliza para aplicar el lado derecho de una disyunción lógica en el 
  objetivo de la prueba. En este caso, se aplica tres veces para llegar al cuarto 
  elemento de la lista. 
  - left se utiliza para aplicar el lado izquierdo de la disyunción lógica y es-
  tablecer que el número 4 es igual al cuarto elemento de la lista.
  - reflexivity se utiliza para demostrar que 4 = 4, es decir, es una igualdad 
  trivial y, por lo tanto, es verdadera.*)
Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl.
  right. right. right. left.
  reflexivity.
Qed.

(*Este lema establece que para cualquier tipo A y B, una función f de A -> B, una lista 
  l de elementos de tipo A y un elemento x de tipo A, si x está en la lista l, entonces 
  f(x) está en la lista resultante de aplicar la función f a cada elemento de l.*)
Lemma In_map :
forall (A B : Type) (f : A -> B) (l : list A) (x : A),
In x l -> In (f x) (map f l).
Proof.
  (*Introducimos las hipótesis y variables cuantificadas en el contexto de la prueba*)
  intros.
  (*Simplificamos la hipótesis H en la forma más simple posible*)
  simpl in H.
  (*Realiza una inducción estructural sobre la lista l. Separamos la lista l en dos goals: 
    el caso base donde l es la lista vacía ([]) y el paso inductivo donde l es de la forma 
    h :: t, esto es; tiene una cabeza h y una cola t*)
  induction l as [|h t HI].
    (*Introducimos las hipótesis y variables cuantificadas en el contexto de la prueba para el 
      caso base*)
  - intros.
    (* Realiza una destrucción por casos en la hipótesis H*)
    destruct H.
    (*Introducimos las hipótesis y variables cuantificadas en el contexto de la prueba para el 
      paso inductivo*)
  - intros.
    (*Realizamos una destrucción por casos en la hipótesis H, donde H1 y H2 representan las dos 
    subcasos generados*)
    destruct H as [H1|H2].
      (*Reemplazamos H1 en el objetivo de la prueba por su equivalente*)
    + rewrite H1.
        (*Establecemos que el lado izquierdo de la disyunción (f x) = (f h) es verdadero*)
        left.
        (*Probamos que ambos lados de la igualdad son, en efecto iguales*)
        reflexivity.
      (*Establecemos que el lado derecho de la disyunción (f x) = (f h) es verdadero*)
    + right.
      (*Aplicamos la hipótesis de inducción al objetivo de la prueba*)
      apply HI.
      (*Aplicamos la hipótesis H2 al objetivo de la prueba*)
      apply H2.
Qed.

(*FixPoint nos indica que esta es una función recursiva, por lo que tendremos:
  Caso Base: La lista es vacía => True
  Recursión: x :: l' descompone la lista en la cabeza x y la cola l'. P x veri-
  fica si la propiedad P se cumple para la cabeza de la lista x. Por el operda-
  dor /\ si la propiedad se cumple para el elemento actual x y para todos los 
  elementos restantes en la cola de la lista l => True.*)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop 
  := match l with
  | [] => True
  | x :: l' => P x /\ All P l'
  end.

(*Este lema establece que para cualquier tipo T, una propiedad P sobre elementos de tipo T y 
  una lista l de elementos de tipo T, la afirmación "para todo x, si x está en l, entonces P 
  x es verdadero" si y sólo si "todos los elementos de l cumplen la propiedad P".*)
Lemma All_In :
forall T (P : T -> Prop) (l : list T),
(forall x, In x l -> P x) <-> All P l.
Proof.
  (*Introducimos las variables cuantificadas en el contexto de la prueba*)
  intros T P l.
  (*Dividimos el objetivo de la prueba en dos subobjetivos correspondientes a la implicación en 
    ambas direcciones, ida y vuelta*)
  split.
  (*Introducimos la hipótesis H en el contexto de la prueba para la implicación hacia la izquierda*)
  - intros H. 
    (*Simplificamos el objetivo de la prueba*)
    simpl.
    (*Realizamos una inducción estructural sobre la lista l. Separamos la lista l en dos goals: el caso 
    base donde l es la lista vacía y el paso inductivo donde l es de la forma x :: l', esto es, tiene 
    una cabeza x y una cola l'*)
    induction l as [|x l' HI].
      (*Resolvemos el subobjetivo correspondiente al caso base utilizando el constructor de la defini-
        ción de All*)
    + constructor.
      (*Resolvemos el subobjetivo correspondiente al paso inductivo utilizando el constructor de la de-
        finición de All*)
    + constructor.
        (*Aplicamos la hipótesis H al objetivo de la prueba*)
      * apply H. 
        (*Establecemos que el lado izquierdo de la conjunción es verdadero*)
        left.
        (*Probamos que ambos lados de la igualdad son iguales*) 
        reflexivity.
        (*Aplicamos la hipótesis de inducción al objetivo de la prueba*)
      * apply HI. 
        (*Introduce las variables cuantificadas en el contexto de la prueba para el paso inductivo*)
        intros y HI'. 
        (*Aplicamos la hipótesis H al objetivo de la prueba*)
        apply H.
        (*Establecemos que el lado derecho de la conjunción es verdadero*)
        right. 
        (*Resolvemos el objetivo actual*)
        assumption.
    (*Introducimos las hipótesis y variables cuantificadas en el contexto de la prueba para la implica-
      ción hacia la derecha*)
  - intros H x HI'. 
    (*Realizamos una inducción estructural sobre la lista l. Separa la lista l en dos goals: el caso 
    base donde l es la lista vacía y el paso inductivo donde l es de la forma y :: l'', esto es, tiene 
    una cabeza y y una cola l''*)
    induction l as [|y l'' HI].
      (*Invertimos la hipótesis HI' para considerar los casos posibles*)
    + inversion HI'.
      (*Simplificamos la hipótesis HI' en la forma más simple posible*)
    + simpl in HI'.
      (*Realizamos una destrucción por casos en la hipótesis HI'*) 
      destruct HI' as [Heq | HI'].
        (*Sustituimos en el objetivo de la prueba todas las ocurrencias de y por x*)
      * subst. 
        (*Invertimos la hipótesis H para obtener más información*)
        inversion H. 
        (*Resolvemos el objetivo actual*)
        assumption.
        (*Aplicamos la hipótesis de inducción al objetivo de la prueba*)
      * apply HI. 
        (*Invertimos la hipótesis H para obtener más información*)
        inversion H. 
        (*Resolvemos el objetivo actual*)
        assumption. 
        (*Resolvemos el objetivo actual*)
        assumption.
Qed.
End Props .

Module Streams .

Variable L : Type.

Inductive TStream :=
   TScons : L -> TStream -> TStream.

(*Definition nos indica que estamos definiendo una función o un valor nuevo, por
  lo que tenemos:
  TScons es un constructor de TStream que toma a la cabeza h y a la cola t. Si s 
  coincide con el patrón TScons h t entonces la función devuelve el valor de h.*)
Definition TShead (s:TStream) : L 
  := match s with
  | TScons h t => h
  end.

(*Definition nos indica que estamos definiendo una función o un valor nuevo, por
  lo que tenemos:
  TScons es un constructor de TStream que toma a la cabeza h y a la cola t. Si s 
  coincide con el patrón TScons h t entonces la función devuelve el valor de t.*)
Definition TStail (s:TStream) : TStream 
  := match s with
  | TScons h t => t
  end.

(*FixPoint nos indica que esta es una función recursiva, por lo que tendremos:
  Caso Base: Si n = 0, entonces se devuelve el primer elemento de s.
  Recursión: Si n coincide con el patrón S k, donde S es el sucesor de un número 
  natural k, entonces la función realiza una llamada recursiva a TSnth con el ín-
  dice k y el resultado de aplicar la función TStail a s.*)
Fixpoint TSnth (n: nat) (s:TStream) : L 
  := match n with 
  | 0 => TShead s
  | S k => TSnth k (TStail s)
  end. 

(*FixPoint nos indica que esta es una función recursiva, por lo que tendremos:
  Caso Base: Si n = 0, entonces se duvuelve s.
  Recursión: Si n coincide con el patrón S k, donde S es el sucesor de un número 
  natural k, entonces la función realiza una llamada recursiva a TSnth_tail con el
  índice k y el resultado de aplicar la función TStail a s.*)
Fixpoint TSnth_tail (n: nat) (s:TStream) : TStream 
  := match n with
  | 0 => s
  | S k => TSnth_tail k (TStail s)
  end.

(*FixPoint nos indica que esta es una función recursiva, por lo que tendremos:
  Caso Base: Si n = 0, entonces se duvuelve s2.
  Recursión: Si n coincide con el patrón S k, donde S es el sucesor de un número 
  natural k, entonces la función realiza una coincidencia de patrones adicional 
  en s1:
    - Si s1 coincide con el patrón TScons h t, donde TScons es un constructor de 
    TStream que toma la cabeza h y la cola t, entonces la función devuelve el re- 
    sultado de TScons h (TSnth_conc k t s2).*)
Fixpoint TSnth_conc (n:nat) (s1 s2:TStream) : TStream 
  := match n with
  | 0 => s2
  | S k => match s1 with
           | TScons h t => TScons h (TSnth_conc k t s2)
           end
  end.

Lemma one_step_nth_tail :
  forall (s : TStream) (n : nat),
  TStail (TSnth_tail n s) = TSnth_tail (S n) s.
Proof.
  intros s n.
  revert s.
  induction n; intros s.
  - simpl. reflexivity.
  - destruct s as [x xs].
    simpl. apply IHn.
Qed.

Lemma multi_step_nth_tail :
  forall (s : TStream) (n : nat),
    TSnth_tail (S n) s = TSnth_tail n (TStail s).
Proof.
  intros s n.
  destruct n as [|n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma multi_step_nth_conc :
  forall (n : nat) (s1 s2 : TStream),
    TSnth_conc (S n) s1 s2 = TSnth_conc n s1 (TScons (TSnth n s1) s2).
Proof.
  intros n s1 s2.
  induction n as [|k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.


Lemma nth_tail_with_nth_conc :
  forall (n : nat) (s1 s2 : TStream),
    TSnth_tail n (TSnth_conc n s1 s2) = s2.
Proof.
  intros n s1 s2.
  revert s1 s2.
  induction n as [|n' IHn]; intros s1 s2.
  - simpl. reflexivity.
  - simpl. assert (TSnth_conc n' (TStail s1) (TScons (TSnth n' (TStail s1)) s2) = TSnth_conc n' (TStail s1) (TScons (TSnth n' (TStail s1)) s2)) as H by reflexivity.
    rewrite <- H. rewrite IHn. reflexivity.
Qed.



Lemma cons_head_tail :
  forall (s : TStream),
  TScons (TShead s) (TStail s) = s.
Proof.
  intros s.
  destruct s as [x xs].
  simpl.
  reflexivity.
Qed.


Lemma nth_conc_with_nth_tail :
  forall (n : nat) (s : TStream),
  TSnth_conc n s (TSnth_tail n s) = s.
Proof.
  intros n s.
  revert s.
  induction n as [|n' IHn]; intros s.
  - simpl. destruct s as [x xs]. reflexivity.
  - destruct s as [x xs]. simpl. rewrite IHn. reflexivity.
Qed.


End Streams .