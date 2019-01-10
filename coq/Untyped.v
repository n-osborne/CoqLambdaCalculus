Require Import List.


(** We need a type for the lambda variables.
    This type should be infinite and the equality should be decidable.
    We make the decidability of the equality an hypothesis.
    The other possibility would have been to create an infinite ad hoc
    type with a decidable equality. This second option would have 
    necessitate type constructors and a proof of the decidability of the
    equality.
*)
Variable A : Type.

Hypothesis A_eq_dec: forall x y: A, {x = y} + {x <> y}.


(** **Type declaration** *)
(** An untyped lambda term is either:
    - a variable from a given Set
    - the abstraction of a variable from a Term
    - the application of a Term to another one.
 *)
Inductive term : Type :=
| var : A -> term
| abs : A -> term -> term
| app : term -> term -> term.

(** **Some functions about terms** *)

(**
We will need a type for the set of variables. There are two sort of possibilities
here:
1. Implement a lightweight type of my own.
2. Use a type from the Coq standard library (e.g. ListSet)
*)

(** My own declaration and lightweight implementation of var_set *)
Definition var_set := list A.

Definition empty_var_set : var_set := nil.

Fixpoint add_var_set (a:A) (s:var_set) : var_set :=
  match s with
  | nil => a::nil
  | h::t =>
    match A_eq_dec a h with
    | left _ => h::t
    | right _ => h::add_var_set a t
    end
  end.

Fixpoint remove_var_set (a:A) (s:var_set) : var_set :=
  match s with
  | nil => nil
  | h::t =>
    match A_eq_dec a h with
    | left _ => t
    | right _ => remove_var_set a t
    end
  end.

Fixpoint in_var_set (a:A) (s:var_set) : bool :=
  match s with
  | nil => false
  | h::t =>
    match A_eq_dec a h with
    | left _ => true
    | right _ => in_var_set a t
    end
  end.

Fixpoint union_var_set (s1:var_set) (s2:var_set) : var_set :=
  match s1 with
  | nil => s2
  | h::t => add_var_set h (union_var_set t s2)
  end.

Fixpoint inter_var_set (s1 s2: var_set) : var_set :=
  match s1 with
  | nil => nil
  | h::t => if in_var_set h s2
           then add_var_set h (inter_var_set t s2)
           else inter_var_set t s2
  end.

Fixpoint minus_var_set (s1 s2: var_set) : var_set :=
  match s2 with
  | nil => s1
  | h::t => if in_var_set h s1
           then minus_var_set (remove_var_set h s1) t
           else minus_var_set s1 t
  end.

(** The ListSet library defines a Predicate set_In 
 This definition relies on the In Predicate for the Lists:
 
 Fixpoint In (a:A) (l:list A) : Prop:=
   match l with
     | [] => False
     | b :: m => b = a \/ In a m
   end.

 *)
Definition var_set_In : A -> var_set -> Prop := In (A:=A).

(** an element is in the var_set it was just add to.
    The proof is more complicated than for simple lists
    as there is an equality test in the add_var_set function.
*)
Theorem in_eq : forall (a:A) (s:var_set), var_set_In a (add_var_set a s).
Proof.
  intros a s. unfold var_set_In. induction s.
  - simpl; left; reflexivity.
  - simpl. destruct (A_eq_dec a a0).
    + rewrite e; simpl; left; reflexivity.
    + simpl; right; apply IHs.
Qed.

(** no element are in the empty_var_set.
    The proof is exactly the same as the one for List,
    which is no surprise as the empty_var_set is an empty List.
*)
Theorem in_nil : forall (a:A), ~ var_set_In a empty_var_set.
Proof.
  intros a; unfold not; intro contra; inversion contra.
Qed.

      
  
(** Function concerning term and var_set *)
Fixpoint get_var_set (t: term) : var_set :=
  match t with
  | (var x) => add_var_set x nil
  | (app t1 t2) => union_var_set (get_var_set t1) (get_var_set t2)
  | (abs x t') => get_var_set t'
  end.

(** Function to get all the free variables of a lambda expression
    The set of the free variables for
    - a lambda variables:         the singleton of the var itelf
    - a lambda abstractions:      the set of free variables of the body minus 
                                  the singleton of the binder
    - a lambda applications:      the union of the sets of free variables of 
                                  the two parts of the applications *)
Fixpoint free_var (t : term) : var_set :=
  match t with
  | (var x) => x :: nil
  | (app t1 t2) => union_var_set (free_var t1) (free_var t2)
  | (abs x t') => remove_var_set x (free_var t')
  end.

(** Some notation for set operations *)
Notation "s + x" := (add_var_set x s)
                       (at level 50, left associativity).
Notation "s - x" := (remove_var_set x s)
                      (at level 50, left associativity).
Notation "x E= s" := (in_var_set x s)
                       (at level 50, left associativity).
Notation "s1 +U+ s2" := (union_var_set s1 s2)
                          (at level 50, left associativity).
Notation "s1 +I+ s2" := (inter_var_set s1 s2)
                          (at level 50, left associativity).
Notation "s1 \ s2" := (minus_var_set s1 s2)
                        (at level 50, left associativity).


Example freevar1 : forall x: A, free_var (var x) = x :: nil.
intro x. reflexivity. Qed.




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

