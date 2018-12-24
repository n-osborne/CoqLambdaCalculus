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

  Lemma lvar_beq_x_x: forall x:lvar, lvar_beq x x = true.
  Proof.
    induction x.
    - reflexivity.
    - simpl; apply IHx.
  Qed.


  Lemma lvar_beq_if_eq: forall x y: lvar, x = y -> (lvar_beq x y) = true.
  Proof.
    intros x y ant; induction x.
    - destruct y.
      + reflexivity.
      + inversion ant.
    - rewrite ant; apply lvar_beq_x_x.
  Qed.

  Lemma lvar_eq_if_beq: forall x y: lvar, (lvar_beq x y) = true -> x = y.
  (* four cases to be considered:
     1. x = lvar0 and y = lvar0   =>  this case is trivial
     2. x = lvar0' and y = S y'   =>  this case works by ex falso
     3. x = S x' and y = lvar0    =>  this case worlks by ex falso
     4. x = S x' and y = S y'     =>  this case should work by induction
                                      but care must be given to the order of the inductions !
*)
  Proof.
    induction x; induction y; intro ant; try trivial; try inversion ant.
    apply eq_xy_implies_eqSxSy_lvar. apply IHx. apply H0.
  Qed.
    
  Lemma lvar_beq_iff_eq: forall x y: lvar, x = y <-> (lvar_beq x y) = true.
  Proof.
    split.
    - apply lvar_beq_if_eq.
    - apply lvar_eq_if_beq.
  Qed.
  

