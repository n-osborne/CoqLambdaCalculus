Module Untyped.

  (** Type declaration
      An untyped lambda term is either:
      - a variable from a given Set
      - the abstraction of a variable from a Term
      - the application of a Term to another one.
   *)
  Inductive Term (X : Set) : Type :=
  | var : X -> Term X
  | abs : X -> Term X -> Term X
  | app : Term X -> Term X -> Term X.

  (* In a perspective of readibility, the type argument is made implicit *)
  Arguments var {X}.
  Arguments abs {X}.
  Arguments app {X}.

  (** Inductive Definition of the redex predicate
      A lambda term is a redex if:
      - it is the application of a lambda term to an abstraction
      - one of its part is a redex*)
  Inductive isRedex {X : Set} : Term X -> Prop :=
  | simpleRedex : forall x:X, forall t1 t2 : (Term X), isRedex (app (abs x t1) t2)
  | indRedex : forall t1 t2 : Term X, (isRedex t1) \/ (isRedex t2) -> isRedex (app t1 t2).
 
 



End Untyped.