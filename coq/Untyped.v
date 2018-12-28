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

Fixpoint get_var_set (t: term) : var_set :=
  match t with
  | (var x) => add_var_set x nil
  | (app t1 t2) => union_var_set (get_var_set t1) (get_var_set t2)
  | (abs x t') => get_var_set t'
  end.

(** Function to get all the free variables of a lambda expression
    The set of the free variables for
    - a lambda variables: the var
    - a lambda abstractions: the set of free variables of the body minus the singleton of       the binder
    - a      lambda applications: the union of the sets of free variables of the two parts of the a   pplications *)
Fixpoint free_var (t : term) : var_set :=
  match t with
  | (var x) => x :: nil
  | (app t1 t2) => union_var_set (free_var t1) (free_var t2)
  | (abs x t') => remove_var_set x (free_var t')
  end.

Example freevar1 : forall x: A, free_var (var x) = x :: nil.
intro x. reflexivity. Qed.



(** Beta-reduction implementation section *)

(** Beta-reduction is the fundamental operation for lambda-calculus. *)
(** On order to implement the beta-reduction on untyped lambda calculus
    we need first to implement a substitution function.

    The main problem is name clashes.
    In order to solve the name clash problem, there are two possibilities:
    1. rename the variable which is the source of the name clash
    2. implement the de Bruijn algorithm
 *)

(**
   **Definition of the renaming**
   x{y/x}       === y
   z{y/x}       === z if x <> z
   (MN){y/x}    === (M{y/x})(N{y/x})
   (\x.M){y/x}  === (\y.(M{y/x}))
   (\z.M){y/x}  === (\z.(M{y/x})) if x <> z
   
 *)
(** Replace all occurrences of x by y in t ie t{y/x} *)
Fixpoint renaming (t: term) (x: A) (y: A) : term :=
  match t with
  | (var z) =>
    match A_eq_dec z x with
    | left _ => var y (* z == x *)
    | right _ => t (* z <> x *)
    end
  | (abs z t') =>
    match A_eq_dec x z with
    | left _ => abs y (renaming t' x y) (* z == x *)
    | right _ => abs z (renaming t' x y) (* z <> x *)
    end
  | (app t1 t2) => app (renaming t1 x y) (renaming t2 x y)
  end.

Notation "t { y / x }" := (renaming t x y)
                       (at level 50, left associativity).

(**
    **Definition of the substitution with renaming**
    x[N/x]       === N
    y[N/x]       === y, if x <> y
    (MP)[N/x]    === (M[N/x])(P[N/x])
    (\x.M)[N/x]  === \x.M
    (\y.M)[N/x]  === \y.(M[N/x]), if x <> y and y not in FV(N)
    (\y.M)[N/x]  === \y'.(M{y'/y}[N/x]), if x <> y, y in FV(N) and y' fresh


 *)
Fixpoint substitution (x: A) (n: term) (t: term) : term :=
  match t with
  | (var y) =>
    match A_eq_dec x y with
    | left _ => n (* x = y *)
    | right _ => t (* x <> y *)
    end
  | (abs y t') =>
    match A_eq_dec x y with (* check whether x is free in t' *)
    | left _ => abs y t' (* x = y, ie x is not free in t' *)
    | right _ => (* x <> y, ie is free in t' *)
      if (in_var_set y (free_var n)) (* name clash *)
      then (* TODO: rename binder in t with a fresh variable *)
      else abs y (substitution x n t')
    end
  | (app t1 t2) => app (substitution x n t1) (substitution x n t2)
  end.
                                             
(** Predicate to determine whether a term is a redex.
    All the work is done when the argument is an application *)
Fixpoint isredex (t: term) : bool :=
  match t with
  | (var x) => false
  | (abs x b) => isredex b
  | (app t1 t2) =>
    match t1 with
    | (var x') => isredex t2
    | (app t1 t2) => orb (isredex t1) (isredex t2)
    | (abs x' b') => orb (invarset x' (freevar b')) (isredex t2)
    end
  end.

