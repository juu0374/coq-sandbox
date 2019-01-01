Require Import Coq.Arith.Arith.

Definition Z := nat.

Definition Even (x : Z) := { y : Z & y + y = x }.
Definition Odd (x : Z) := { y : Z & S (y + y) = x }.

Definition Even_or_Odd : forall x, Even x + Odd x.
Proof.
  induction x.
  left.
  exists 0.
  reflexivity.
  induction IHx.
  right.
  exists (projT1 a).
  apply f_equal.
  apply (projT2 a).
  left.
  exists (S (projT1 b)).
  simpl.
  apply f_equal.
  induction (plus_n_Sm (projT1 b) (projT1 b)).
  apply (projT2 b).
Defined.

Definition even (n : nat) : Z := n + n.
Definition odd (n : nat) : Z := S (n + n).

Definition Zsplit' (P : Z -> Type)
 (e : forall n, P (even n)) (o : forall n, P (odd n)) (x : Z) : P x.
Proof.
  destruct (Even_or_Odd x).
  rewrite <- (projT2 e0).
  apply (e (projT1 e0)).
  rewrite <- (projT2 o0).
  apply (o (projT1 o0)).
Defined.

Definition zero := 0.
Definition pos (n : nat) : Z := S (S (n + n)).
Definition neg (n : nat) : Z := S (n + n).

Definition Zsplit (P : Z -> Type) (z : P 0)
 (p : forall n, P (pos n)) (n : forall n, P (neg n)) (x : Z) : P x.
Proof.
  destruct x.
  apply z.
  apply (Zsplit' (fun x => P (S x))).
  apply n.
  apply p.
Defined.

Definition Zsucc : Z -> Z :=
  Zsplit (fun _ => Z) (pos 0) (fun x => pos (S x)) (fun y =>
    match y with O => zero | S y => neg y end).

Definition Zpred : Z -> Z :=
  Zsplit (fun _ => Z) (neg 0) (fun x =>
    match x with O => zero | S x => pos x end) (fun y => neg (S y)).

Lemma pos_S n : pos (S n) = S (S (pos n)).
Proof.
  unfold pos.
  simpl.
  apply f_equal.
  apply f_equal.
  apply f_equal.
  symmetry.
  apply plus_n_Sm.
Qed.

Definition lem : forall x y, x + x = y + y -> x = y.
Proof.
  induction x.
  simpl.
  induction y.
  reflexivity.
  discriminate.
  induction y.
  discriminate.
  simpl.
  intros.
  apply f_equal.
  rewrite <- plus_n_Sm in H.
  rewrite <- plus_n_Sm in H.
  apply (f_equal pred) in H.
  apply (f_equal pred) in H.
  simpl in H.
  apply IHx.
  apply H.
Defined.

Require Import Coq.Arith.Peano_dec.

Lemma lem2 : forall a b, S a = b + b -> b <> 0.
Proof.
  intros.
  intro.
  rewrite H0 in H.
  discriminate.
Qed.

Lemma neq_0_r : forall n : nat, n <> 0 -> { m : nat & n = S m }.
Proof.
  intros.
  induction n.
  exfalso.
  apply H.
  reflexivity.
  exists n.
  reflexivity.
Qed.

Lemma even_is_not_odd x : Odd (even x) -> False.
Proof.
  induction x.
  intro.
  destruct H.
  discriminate.
  intro.
  destruct H.
  apply (f_equal pred) in e.
  simpl in e.
  rewrite <- plus_n_Sm in e.
  specialize (lem2 _ _ (eq_sym e)).
  intro.
  specialize (neq_0_r x0).
  intro.
  specialize (H0 H).
  destruct H0.
  rewrite e0 in e.
  rewrite <- plus_n_Sm in e.
  apply (f_equal pred) in e.
  simpl in e.
  apply IHx.
  exists x1.
  apply e.
Qed.

Lemma odd_is_not_even x : Even (odd x) -> False.
Proof.
  intro.
  induction x.
  induction H.
  unfold odd in p.
  induction x.
  discriminate.
  rewrite <- plus_n_Sm in p.
  discriminate.
  unfold Even, odd in *.
  induction H.
  rewrite <- plus_n_Sm in p.
  simpl in p.
  specialize (lem2 _ _ (eq_sym p)).
  specialize (neq_0_r x0).
  intros.
  specialize (H H0).
  destruct H.
  rewrite e in p.
  simpl in p.
  rewrite <- plus_n_Sm in p.
  do 2 apply (f_equal pred) in p.
  simpl in p.
  apply IHx.
  exists x1.
  apply p.
Qed.

Lemma Zsplit'_beta_even : forall P e o x, Zsplit' P e o (even x) = e x.
Proof.
  intros.
  unfold Zsplit'.
  destruct (Even_or_Odd (even x)).
  destruct e0.
  simpl.
  specialize (lem _ _ e0).
  intro.
  induction H.
  induction (UIP_nat _ _ eq_refl e0).
  reflexivity.
  exfalso.
  apply (even_is_not_odd x).
  apply o0.
Qed.

Lemma Zsplit'_beta_odd : forall P e o x, Zsplit' P e o (odd x) = o x.
Proof.
  intros.
  unfold Zsplit'.
  destruct (Even_or_Odd (odd x)).
  exfalso.
  apply (odd_is_not_even x).
  apply e0.
  destruct o0.
  simpl.
  unfold odd in e0.
  generalize e0.
  apply (f_equal pred) in e0.
  simpl in e0.
  apply lem in e0.
  destruct e0.
  intro.
  induction (UIP_nat _ _ eq_refl e0).
  reflexivity.
Qed.

Lemma Zsplit_beta_pos : forall P z p n x, Zsplit P z p n (pos x) = p x.
Proof.
  intros.
  simpl.
  apply (Zsplit'_beta_odd (fun x0 : Z => P (S x0)) n p x).
Qed.

Lemma Zsplit_beta_neg : forall P z p n x, Zsplit P z p n (neg x) = n x.
Proof.
  intros.
  simpl.
  apply (Zsplit'_beta_even (fun x0 : Z => P (S x0)) n p x).
Qed.

Lemma Zsucc_pos_S n : Zsucc (pos n) = pos (S n).
Proof.
  apply (Zsplit_beta_pos (fun _ : Z => Z) _ (fun x : nat => pos (S x)) _).
Qed.

Lemma Zpred_neg_S n : Zpred (neg n) = neg (S n).
Proof.
  apply (Zsplit_beta_neg (fun _ : Z => Z) _ _ (fun y : nat => neg (S y))).
Qed.

Definition Zind (P : Z -> Type) (z : P 0) (s : forall n, P n -> P (Zsucc n))
(p : forall n, P n -> P (Zpred n)) (n : Z) : P n.
Proof.
  apply Zsplit.
  apply z.
  induction n0.
  apply (s 0 z).
  rewrite <- Zsucc_pos_S.
  apply (s _ IHn0).
  induction n0.
  apply (p 0 z).
  rewrite <- Zpred_neg_S.
  apply (p _ IHn0).
Defined.

Definition Zrec (P : Type) (z : P) (s : P -> P) (p : P -> P) : Z -> P :=
  Zind (fun _ => P) z (fun _ => s) (fun _ => p).

Lemma Zrec_beta_succ (P : Type) (z : P) (s : P -> P) (p : P -> P) 
              (i2 : forall (m : P), m = s (p m)) (n : Z)
: Zrec P z s p (Zsucc n) = s (Zrec P z s p n).
Proof.
  apply (Zsplit (fun n => Zrec P z s p (Zsucc n) = s (Zrec P z s p n))).
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ 0).
  reflexivity.
  intro.
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ n0).
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ n0).
  rewrite (Zsplit'_beta_odd _ _ _ (S n0)).
  simpl.
  destruct (Zsucc_pos_S n0).
  simpl.
  reflexivity.
  intro.
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ n0).
  rewrite (Zsplit'_beta_even _ _ _ n0).
  simpl.
  destruct n0.
  simpl.
  apply i2.
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ n0).
  destruct (Zpred_neg_S n0).
  simpl.
  apply i2.
Qed.

Lemma Zrec_beta_pred (P : Type) (z : P) (s : P -> P) (p : P -> P) 
              (i1 : forall (m : P), m = p (s m)) (n : Z)
: Zrec P z s p (Zpred n) = p (Zrec P z s p n).
Proof.
  apply (Zsplit (fun n => Zrec P z s p (Zpred n) = p (Zrec P z s p n))).
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ 0).
  reflexivity.
  intro.
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ n0).
  rewrite (Zsplit'_beta_odd _ _ _ n0).
  destruct n0.
  simpl.
  apply i1.
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ n0).
  destruct (Zsucc_pos_S n0).
  simpl.
  apply i1.
  intro.
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ n0).
  rewrite (Zsplit'_beta_even _ _ _ n0).
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ (S n0)).
  simpl.
  destruct (Zpred_neg_S n0).
  reflexivity.
Qed.

Definition Zplus x : Z -> Z :=
  Zrec Z x Zsucc Zpred.

Lemma Zsucc_Zpred x : x = Zsucc (Zpred x).
Proof.
  apply (Zsplit (fun x => x = Zsucc (Zpred x))).
  reflexivity.
  intros.
  symmetry.
  unfold Zpred.
  rewrite Zsplit_beta_pos.
  destruct n.
  reflexivity.
  apply Zsucc_pos_S.
  unfold Zsucc.
  intros.
  symmetry.
  unfold Zpred.
  rewrite Zsplit_beta_neg.
  apply (Zsplit_beta_neg (fun _ : Z => Z) _ _
  (fun y : nat => match y with
                  | 0 => zero
                  | S y0 => neg y0
                  end)).
Qed.

Lemma Zpred_Zsucc x : x = Zpred (Zsucc x).
Proof.
  apply (Zsplit (fun x => x = Zpred (Zsucc x))).
  reflexivity.
  unfold Zsucc.
  symmetry.
  rewrite Zsplit_beta_pos.
  unfold Zpred.
  apply (Zsplit_beta_pos (fun _ : Z => Z) _
  (fun x0 : nat => match x0 with
                   | 0 => zero
                   | S x1 => pos x1
                   end) _).
  symmetry.
  unfold Zsucc.
  rewrite Zsplit_beta_neg.
  destruct n.
  reflexivity.
  apply Zpred_neg_S.
Qed.

Lemma Zplus_x_Sy (x y : Z) : Zplus x (Zsucc y) = Zsucc (Zplus x y).
Proof.
  unfold Zplus.
  apply Zrec_beta_succ.
  apply Zsucc_Zpred.
Qed.

Lemma Zplus_x_Py (x y : Z) : Zplus x (Zpred y) = Zpred (Zplus x y).
Proof.
  unfold Zplus.
  apply Zrec_beta_pred.
  apply Zpred_Zsucc.
Qed.

Lemma Zplus_0n : forall n, Zplus zero n = n.
Proof.
  apply Zind.
  reflexivity.
  simpl.
  intros.
  rewrite Zplus_x_Sy.
  apply f_equal.
  apply H.
  intros.
  rewrite Zplus_x_Py.
  apply f_equal.
  apply H.
Qed.

Lemma Zplus_Sx_y (x y : Z) : Zplus (Zsucc x) y = Zsucc (Zplus x y).
Proof.
  apply (Zind (fun y => Zplus (Zsucc x) y = Zsucc (Zplus x y))).
  reflexivity.
  intros.
  rewrite Zplus_x_Sy.
  rewrite Zplus_x_Sy.
  apply f_equal.
  apply H.
  intros.
  rewrite Zplus_x_Py.
  rewrite Zplus_x_Py.
  rewrite H.
  rewrite <- Zpred_Zsucc.
  apply Zsucc_Zpred.
Qed.

Lemma Zplus_Px_y (x y : Z) : Zplus (Zpred x) y = Zpred (Zplus x y).
Proof.
  apply (Zind (fun y => Zplus (Zpred x) y = Zpred (Zplus x y))).
  reflexivity.
  intros.
  rewrite Zplus_x_Sy.
  rewrite Zplus_x_Sy.
  rewrite H.
  rewrite <- Zsucc_Zpred.
  apply Zpred_Zsucc.
  intros.
  rewrite Zplus_x_Py.
  rewrite Zplus_x_Py.
  apply f_equal.
  apply H.
Qed.

Lemma Zplus_comm : forall x y, Zplus x y = Zplus y x.
Proof.
  intros.
  apply (Zind (fun x => Zplus x y = Zplus y x)).
  simpl.
  apply Zplus_0n.
  intros.
  rewrite Zplus_x_Sy.
  rewrite Zplus_Sx_y.
  apply f_equal.
  apply H.
  intros.
  rewrite Zplus_x_Py.
  rewrite Zplus_Px_y.
  apply f_equal.
  apply H.
Qed.

Lemma Zplus_assoc : forall x y z, Zplus (Zplus x y) z = Zplus x (Zplus y z).
Proof.
  intros.
  apply (Zind (fun z => Zplus (Zplus x y) z = Zplus x (Zplus y z))).
  reflexivity.
  intros.
  do 3 rewrite Zplus_x_Sy.
  apply f_equal.
  apply H.
  intros.
  do 3 rewrite Zplus_x_Py.
  apply f_equal.
  apply H.
Qed.

Definition Zneg : Z -> Z := Zsplit (fun _ => Z) zero neg pos.

Lemma Zneg_S n : Zneg (Zsucc n) = Zpred (Zneg n).
Proof.
  apply (Zsplit (fun n => Zneg (Zsucc n) = Zpred (Zneg n))).
  simpl.
  apply (Zsplit'_beta_odd (fun _ : Z => Z) _ _ 0).
  simpl.
  intros.
  rewrite (Zsplit'_beta_odd _ _ _ n0).
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ (S n0)).
  rewrite (Zsplit'_beta_odd _ _ _ n0).
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ n0).
  reflexivity.
  simpl.
  intros.
  rewrite (Zsplit'_beta_even _ _ _ n0).
  destruct n0.
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ 0).
  reflexivity.
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ n0).
  rewrite (Zsplit'_beta_even _ _ _ (S n0)).
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ (S n0)).
  reflexivity.
Qed.

Lemma Zneg_P n : Zneg (Zpred n) = Zsucc (Zneg n).
Proof.
  apply (Zsplit (fun n => Zneg (Zpred n) = Zsucc (Zneg n))).
  reflexivity.
  simpl.
  intros.
  do 2 rewrite (Zsplit'_beta_odd _ _ _ n0).
  destruct n0.
  reflexivity.
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ n0).
  rewrite (Zsplit'_beta_even _ _ _ (S n0)).
  reflexivity.
  simpl.
  intro.
  do 2 rewrite (Zsplit'_beta_even _ _ _ n0).
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ (S n0)).
  rewrite (Zsplit'_beta_odd _ _ _ n0).
  reflexivity.
Qed.

Lemma Zplus_neg_x : forall x, Zplus (Zneg x) x = zero.
Proof.
  intro.
  apply (Zind (fun x => Zplus (Zneg x) x = zero)).
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite Zplus_x_Sy.
  rewrite Zneg_S.
  rewrite Zplus_Px_y.
  rewrite <- Zsucc_Zpred.
  apply H.
  intros.
  rewrite Zplus_x_Py.
  rewrite Zneg_P.
  rewrite Zplus_Sx_y.
  rewrite <- Zpred_Zsucc.
  apply H.
Qed.

Lemma Zplus_x_neg : forall x, Zplus x (Zneg x) = zero.
Proof.
  intro.
  rewrite Zplus_comm.
  apply Zplus_neg_x.
Qed.

Lemma Zneg_neg x : Zneg (Zneg x) = x.
Proof.
  apply (Zsplit (fun x => Zneg (Zneg x) = x)).
  reflexivity.
  intro.
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ n).
  simpl.
  apply (Zsplit'_beta_even (fun _ => Z)).
  intro.
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ n).
  simpl.
  apply (Zsplit'_beta_odd (fun _ => Z)).
Qed.

Definition Zmult (x : Z) : Z -> Z := Zrec Z zero (Zplus x) (Zplus (Zneg x)).

Infix "+" := Zplus.
Infix "*" := Zmult.
Notation "- x" := (Zneg x).

Lemma Zmult_x_Sy x y : Zmult x (Zsucc y) = Zplus x (Zmult x y).
Proof.
  unfold Zmult.
  apply Zrec_beta_succ.
  intro.
  apply (Zind (fun x => m = Zplus x (Zplus (Zneg x) m))).
  simpl.
  symmetry.
  rewrite Zplus_0n.
  apply Zplus_0n.
  intros.
  rewrite Zplus_Sx_y.
  rewrite Zneg_S.
  rewrite Zplus_Px_y.
  rewrite Zplus_x_Py.
  rewrite <- Zsucc_Zpred.
  apply H.
  intros.
  rewrite Zplus_Px_y.
  rewrite Zneg_P.
  rewrite Zplus_Sx_y.
  rewrite Zplus_x_Sy.
  rewrite <- Zpred_Zsucc.
  apply H.
Qed.

Definition Zmult_x_Py x y : Zmult x (Zpred y) = Zplus (Zneg x) (Zmult x y).
Proof.
  unfold Zmult.
  apply Zrec_beta_pred.
  intro.
  apply (Zind (fun x => m = Zplus (Zneg x) (Zplus x m))).
  simpl.
  symmetry.
  rewrite Zplus_0n.
  apply Zplus_0n.
  intros.
  rewrite Zneg_S.
  rewrite Zplus_Px_y.
  rewrite Zplus_Sx_y.
  rewrite Zplus_x_Sy.
  rewrite <- Zpred_Zsucc.
  apply H.
  intros.
  rewrite Zneg_P.
  rewrite Zplus_Sx_y.
  rewrite Zplus_Px_y.
  rewrite Zplus_x_Py.
  rewrite <- Zsucc_Zpred.
  apply H.
Qed.

Lemma Zmult_0n n : Zmult 0 n = 0.
Proof.
  apply (Zind (fun n => Zmult 0 n = 0)).
  reflexivity.
  intros.
  rewrite Zmult_x_Sy.
  rewrite Zplus_0n.
  apply H.
  intros.
  rewrite Zmult_x_Py.
  simpl.
  rewrite Zplus_0n.
  apply H.
Qed.

Lemma Zmult_1n n : Zmult (pos 0) n = n.
Proof.
  apply (Zind (fun n => Zmult (pos 0) n = n)).
  simpl.
  reflexivity.
  intros.
  rewrite Zmult_x_Sy.
  rewrite H.
  rewrite Zplus_comm.
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ 0).
  reflexivity.
  intros.
  rewrite Zmult_x_Py.
  simpl.
  rewrite (Zsplit'_beta_odd _ _ _ 0).
  rewrite Zplus_comm.
  simpl.
  rewrite (Zsplit'_beta_even _ _ _ 0).
  simpl.
  apply f_equal.
  apply H.
Qed.

Lemma Zmult_Sx_y x y : Zmult (Zsucc x) y = Zplus y (Zmult x y).
Proof.
  intros.
  apply (Zind (fun y => Zmult (Zsucc x) y = Zplus y (Zmult x y))).
  reflexivity.
  intros.
  repeat rewrite Zmult_x_Sy.
  repeat rewrite Zplus_Sx_y.
  apply f_equal.
  rewrite H.
  rewrite <- Zplus_assoc.
  replace (Zplus x n) with (Zplus n x).
  apply Zplus_assoc.
  apply Zplus_comm.
  intros.
  repeat rewrite Zmult_x_Py.
  rewrite Zneg_S.
  repeat rewrite Zplus_Px_y.
  apply f_equal.
  rewrite H.
  rewrite <- Zplus_assoc.
  replace (Zplus (- x) n) with (Zplus n (- x)).
  apply Zplus_assoc.
  apply Zplus_comm.
Qed.

Lemma Zmult_Px_y x y : Zmult (Zpred x) y = Zplus (Zneg y) (Zmult x y).
Proof.
  apply (Zind (fun y => Zmult (Zpred x) y = Zplus (Zneg y) (Zmult x y))).
  reflexivity.
  intros.
  repeat rewrite Zmult_x_Sy.
  rewrite Zneg_S.
  repeat rewrite Zplus_Px_y.
  apply f_equal.
  rewrite H.
  rewrite <- Zplus_assoc.
  replace (Zplus x (- n)) with (Zplus (- n) x).
  apply Zplus_assoc.
  apply Zplus_comm.
  intros.
  repeat rewrite Zmult_x_Py.
  repeat rewrite Zneg_P.
  repeat rewrite Zplus_Sx_y.
  apply f_equal.
  rewrite H.
  rewrite <- Zplus_assoc.
  replace (Zplus (- x) (- n)) with (Zplus (- n) (- x)).
  apply Zplus_assoc.
  apply Zplus_comm.
Qed.

Lemma Zmult_comm x y : Zmult x y = Zmult y x.
Proof.
  apply (Zind (fun x => Zmult x y = Zmult y x)).
  simpl.
  apply Zmult_0n.
  intros.
  rewrite Zmult_Sx_y.
  rewrite Zmult_x_Sy.
  apply f_equal.
  apply H.
  intros.
  rewrite Zmult_Px_y.
  rewrite Zmult_x_Py.
  apply f_equal.
  apply H.
Qed.

Lemma Zmult_plus_distr_r x y z :
 Zmult (Zplus x y) z = Zplus (Zmult x z) (Zmult y z).
Proof.
  apply (Zind (fun x => Zmult (Zplus x y) z = Zplus (Zmult x z) (Zmult y z))).
  rewrite Zmult_0n.
  rewrite Zplus_0n.
  symmetry.
  apply Zplus_0n.
  intros.
  rewrite Zplus_Sx_y.
  repeat rewrite Zmult_Sx_y.
  rewrite H.
  symmetry.
  apply Zplus_assoc.
  intros.
  rewrite Zplus_Px_y.
  repeat rewrite Zmult_Px_y.
  rewrite H.
  symmetry.
  apply Zplus_assoc.
Qed.

Lemma Zmult_plus_distr_l x y z :
Zmult x (Zplus y z) = Zplus (Zmult x y) (Zmult x z).
Proof.
  rewrite Zmult_comm.
  replace (Zmult x y) with (Zmult y x).
  replace (Zmult x z) with (Zmult z x).
  apply Zmult_plus_distr_r.
  apply Zmult_comm.
  apply Zmult_comm.
Qed.

Lemma Zplus_neg x y : Zplus (Zneg x) (Zneg y) = Zneg (Zplus x y).
Proof.
  apply (Zind (fun y => Zplus (- x) (- y) = - Zplus x y)).
  reflexivity.
  intros.
  rewrite Zneg_S.
  rewrite Zplus_x_Py.
  rewrite Zplus_x_Sy.
  rewrite Zneg_S.
  apply f_equal.
  apply H.
  intros.
  rewrite Zneg_P.
  rewrite Zplus_x_Sy.
  rewrite Zplus_x_Py.
  rewrite Zneg_P.
  apply f_equal.
  apply H.
Qed.

Lemma Zmult_neg_l x y : Zmult (Zneg x) y = Zneg (Zmult x y).
Proof.
  apply (Zind (fun y => Zmult (- x) y = - Zmult x y)).
  reflexivity.
  intros.
  rewrite Zmult_x_Sy.
  rewrite Zmult_x_Sy.
  rewrite H.
  apply Zplus_neg.
  intros.
  repeat rewrite Zmult_x_Py.
  rewrite H.
  apply Zplus_neg.
Qed.

Lemma Zmult_neg_r x y : Zmult x (Zneg y) = Zneg (Zmult x y).
Proof.
  rewrite Zmult_comm.
  rewrite Zmult_neg_l.
  apply f_equal.
  apply Zmult_comm.
Qed.

Lemma Zmult_assoc x y z : Zmult (Zmult x y) z = Zmult x (Zmult y z).
Proof.
  apply (Zind (fun z => Zmult (Zmult x y) z = Zmult x (Zmult y z))).
  reflexivity.
  intros.
  repeat rewrite Zmult_x_Sy.
  rewrite H.
  symmetry.
  apply Zmult_plus_distr_l.
  intros.
  repeat rewrite Zmult_x_Py.
  rewrite H.
  rewrite Zmult_plus_distr_l.
  rewrite Zmult_neg_r.
  reflexivity.
Qed.