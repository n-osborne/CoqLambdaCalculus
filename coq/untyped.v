Module Untyped.


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

  (** Some basic properties on the inductive definition of lvar. 
      Mainly, equality is decidable. *)
  Lemma eq_SxSy_implies_eq_xy_lvar : forall x y: lvar, S x = S y -> x = y.
  Proof.
    induction x.
    - induction y.
      + intro; reflexivity.
      + intro H. inversion H.
    - induction y.
      + intro H. inversion H.
      + intro H. inversion H. reflexivity.
  Qed.

  Lemma eq_xy_implies_eqSxSy_lvar : forall x y: lvar, x = y -> S x = S y.
    induction x; induction y.
    - intro; reflexivity.
    - intro H; inversion H.
    - intro H; inversion H.
    - intro H; inversion H; reflexivity.
  Qed.

  Lemma eq_dec_lvar : forall x y : lvar, {x = y} + {x <> y}.
  Proof.
    induction x; destruct y.
    - left; reflexivity.
    - right; unfold not; intro H; inversion H.
    - right; unfold not; intro H; inversion H.
    - destruct (IHx y); [left|right].
      + apply eq_xy_implies_eqSxSy_lvar. apply e.
      + unfold not; intro H. inversion H. auto.
  Qed.
      
  (** *Type declaration for the sets of variable.*
      Variables are strings, mainly in order to have an infinite
      set of available variables according to the definition of
      the syntax of lambda calculus. *)
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

  Fixpoint union (s1: varset) (s2: varset) : varset :=
    match s2 with
    | nil => s1
    | h::t => union (h::s1) t
    end.

  Notation "s1 ++ s2" := (union s1 s2).
  
  Fixpoint invarset (el: lvar) (s: varset) : bool :=
    match s with
    | nil => false
    | h::t => if lvar_beq el h then true else invarset el t
    end.

  Fixpoint removevar (el: lvar) (s: varset) : varset :=
    match s with
    | nil => nil
    | h::t => if lvar_beq el h then t else h::(removevar el t)
    end.

  Notation "x \ s" := (removevar x s)
                        (at level 60, right associativity).

  
  (** *Type declaration*
      An untyped lambda term is either:
      - a variable from a given Set
      - the abstraction of a variable from a Term
      - the application of a Term to another one.
   *)
  Inductive term : Type :=
  | var : lvar -> term
  | abs : lvar -> term -> term
  | app : term -> term -> term.

  (** *Some functions about terms* *)

  (** Function to get all the variables of a lambda expression *)
  Fixpoint getvarset (t: term) : varset :=
      match t with
      | (var x) => x :: nil
      | (app t1 t2) => (getvarset t1) ++ (getvarset t2)
      | (abs x t') => getvarset t'
      end.

  (** Function to get all the free variables of a lambda expression
      The set of the free variables for
      - a lambda variables: the var
      - a lambda abstractions: the set of free variables of the body minus the singleton of the binder
      - a lambda applications: the union of the sets of free variables of the two parts of the applications *)
  Fixpoint freevar (t : term) : varset :=
    match t with
    | (var x) => x :: nil
    | (app t1 t2) => (freevar t1) ++ (freevar t2)
    | (abs x t') => x \ (freevar t')
    end.

  Example freevar1 : forall x: lvar, freevar (var x) = [x].
  intro x. reflexivity. Qed.

  Example freevar2 : forall x y : lvar, freevar (app (var x) (var y)) = x::y::nil
  \/ freevar (app (var x) (var y)) = y::x::nil.
  Proof. intros. simpl. right. reflexivity. Qed.

  Example freevar3 : forall x y : lvar, x <> y -> freevar (abs x (var y)) = [y].
  Proof. intros. unfold not in H. simpl. destruct (lvar_beq x y).
         -  admit.
         - reflexivity.
  Admitted.
  
  (** Predicate to determine whether a term is a redex.
      All the work is done when the argument is an application *)
  Fixpoint isredex (t: term) : bool :=
    match t with
    | (var x) => false
    | (abs x b) => isredex b
    | (app t1 t2) => match t1 with
                     | (var x') => isredex t2
                     | (app t1 t2) => orb (isredex t1) (isredex t2)
                     | (abs x' b') => orb (invarset x' (freevar b')) (isredex t2)
                    end
    end.




End Untyped.
