module Prop where

data Prop = Var String | Cons Bool| Not Prop
          | And Prop Prop | Or Prop Prop
          | Impl Prop Prop | Syss Prop Prop
          deriving (Show, Eq)

fnn :: Prop -> Prop
fnn (Var p) = Var p
fnn (Syss p q) = And (fnn(Impl p q)) (fnn(Impl q p))
fnn (Impl p q) = Or (fnn(Not p)) (fnn q)
fnn (Not (Or p q)) = And (fnn(Not p)) (fnn(Not q))
fnn (Not (And p q)) = Or (fnn(Not p)) (fnn(Not q))
fnn (Not (Not p)) = fnn p
fnn (Not (Cons True)) = Cons False
fnn (Not (Cons False)) = Cons True
fnn (Not p) = Not (fnn p)
fnn (Or p q) = Or (fnn p) (fnn q)
fnn (And p q) = And (fnn p) (fnn q)
fnn (Cons True) = Cons True
fnn (Cons False) = Cons False

fnc :: Prop -> Prop
fnc = distributeOr . fnn

distributeOr :: Prop -> Prop
distributeOr (Or p (And q s)) = And (Or (distributeOr p) (distributeOr q)) (Or (distributeOr p) (distributeOr s))
distributeOr (Or (And p q) s) = And (Or (distributeOr p) (distributeOr s)) (Or (distributeOr q) (distributeOr s))
distributeOr (Or p q) = Or (distributeOr p) (distributeOr q)
distributeOr (And p q) = And (distributeOr p) (distributeOr q)
distributeOr p = p
