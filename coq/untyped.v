Module Untyped.


  Section Utils.

    (** Type declaration for the variables.

    According to the syntax of lambda calculus, we need an infinite
    set of variables. *)
    Inductive lvar : Type :=
    | lvarO : lvar
    | S : lvar -> lvar.

    Fixpoint lvar_beq (x: lvar) (y: lvar) : bool :=
      match x with
      | lvarO => match y with
                | lvarO => true
                | S y' => false
                end
      | S x' => match y with
               | lvarO => false
               | S y' => lvar_beq x' y'
               end
      end.
    
    (** Type declaration for the sets of variable.
     
     Variables are strings, mainly in order to have an infinite
     set of available variables according to the definition of
     the syntax of lambda calculus.
     
     *)
    Inductive varset : Type := 
    | nil : varset
    | cons : lvar -> varset -> varset.

    Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
    Notation "[ ]" := nil.
    Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

    Fixpoint addvar  (el : lvar) (s : varset) : varset :=
      match s with
      | nil => el :: nil
      | h::t => if lvar_beq h el then t else h::(addvar el t)
      end.

    Fixpoint concat (s1: varset) (s2: varset) : varset :=
      match s2 with
      | nil => s1
      | h::t => concat (h::s1) t
      end.
    
    Fixpoint removevar (el: lvar) (s: varset) : varset :=
      match s with
      | nil => nil
      | h::t => if lvar_beq el h then t else h::(removevar el t)
      end.
    
  End Utils.
  
  (** Type declaration
      An untyped lambda term is either:
      - a variable from a given Set
      - the abstraction of a variable from a Term
      - the application of a Term to another one.
   *)
  Inductive Term : Type :=
  | var : lvar -> Term
  | abs : lvar -> Term -> Term
  | app : Term -> Term -> Term.


  (** Inductive Definition of the redex predicate
      A lambda term is a redex if:
      - it is the application of a lambda term to an abstraction
      - one of its part is a redex*)
  Inductive isRedex : Term -> Prop :=
  | simpleRedex : forall x : lvar, forall t1 t2 : Term, isRedex (app (abs x t1) t2)
  | indRedex : forall t1 t2 : Term, (isRedex t1) \/ (isRedex t2) -> isRedex (app t1 t2).
 
  (** Function to get all the free variables of a lambda expression
      The set of the free variables for
      - a lambda variables: the var
      - a lambda abstractions: the set of free variables of the body minus the singleton of the binder
      - a lambda applications: the union of the sets of free variables of the two parts of the applications
   *)
  Fixpoint freevar (t : Term) : varset :=
    match t with
    | (var x) => cons x nil
    | (app t1 t2) => concat (freevar t1) (freevar t2)
    | (abs x t') => removevar x (freevar t')
    end.


End Untyped.