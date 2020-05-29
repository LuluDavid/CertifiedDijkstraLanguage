(* Préambule nat *)

(* Soustraction dans nat (sub, noté -) *)

Require Export Nat.
Require Export Le Lt.

(* Nommage suivant le type de f
 * - simplication à gauche ou à droite, addition à gauche ou à droite, 
 * - prédécesseur, succeseur, opposé, suivant, décalage  
 * equation 1 -> equation 2
 * operation = total -> f operation = f total
 * Remarque : une soustraction nulle vaut en fait (- d), pour un certain d.
 *)

Lemma simplificationGaucheAddition :
  forall m n p,
  m + n = p -> n = p - m.
Proof.
  intros.
  symmetry.
  apply PeanoNat.Nat.add_sub_eq_l.
  assumption.
Qed.

Lemma simplificationDroiteAddition :
  forall m n p,
    m + n = p -> m = p - n.
Proof.
  intros.
  symmetry.
  apply PeanoNat.Nat.add_sub_eq_r.
  assumption.
Qed.

Lemma simplificationDroiteSoustractionNonNulle :
  forall m n p,
    m - n = S p -> m = S p + n.
Proof.
  fix HR 1.
  intros m n p H.
  destruct m as [ | pm].
  {
    simpl in H.
    discriminate H.
  }
  {
    simpl.
    f_equal.
    destruct n as [ | pn].
    {
      injection H; intro H'.
      rewrite PeanoNat.Nat.add_0_r.
      assumption.
    }
    {
      simpl in H.
      rewrite <- PeanoNat.Nat.add_succ_comm.
      apply HR.
      assumption.
    }
  }
Qed.

Lemma additionGaucheSoustractionNonNulle :
  forall m n p d,
    m - n = S p -> (d + m) - n = d + S p.
Proof.
  fix HR 1.
  intros m n p d.
  destruct m as [ | pm].
  {
    simpl.
    intro H; discriminate H.
  }
  {
    destruct n as [ | pn].
    {
      simpl.
      intro H.
      injection H; intro H'.
      rewrite H'.
      rewrite PeanoNat.Nat.sub_0_r.
      reflexivity.
    }
    {
      simpl.
      intro H.
      rewrite <- PeanoNat.Nat.add_succ_comm.
      simpl.
      apply HR.
      assumption.
    }
  }
Qed.

(* - soustraction nulle : m - n = -d
 * - oppose : n - m = d
 * - simplification droite : n = d + m
*)
Lemma simplificationDroiteOpposeSoustractionNulle :
  forall m n,
    m - n = 0 -> exists d, n = d + m.
Proof.
  fix HR 1.
  intros m n H.
  destruct m as [ | pm].
  {
    exists n.
    symmetry.
    apply PeanoNat.Nat.add_0_r.
  }
  {
    destruct n as [ | pn].
    {
      discriminate H.
    }
    {
      simpl in H.
      destruct (HR pm pn) as [d ccl].
      assumption.
      exists d.
      rewrite <- PeanoNat.Nat.add_succ_comm.
      simpl.
      f_equal.
      assumption.
    }
  }
Qed.

Lemma opposeSimplificationDroiteAddition :
  forall m n d,
    d + m = n
    -> 0 = m - n.
Proof.
  fix HR 1.
  intros m n d H.
  destruct m as [ | pm].
  {
    simpl.
    reflexivity.
  }
  {
    destruct n as [ | pn].
    {
      rewrite <- PeanoNat.Nat.add_succ_comm in H.
      simpl in H.
      discriminate H.
    }
    {
      rewrite <- PeanoNat.Nat.add_succ_comm in H.
      simpl in H.
      injection H; intro H'.
      simpl.
      apply HR with d.
      assumption.
    }
  }
Qed.

Lemma casEgaliteSoustractionNulle :
  forall m n d,
    m - n = 0 -> S m - n = S d -> m = n /\ d = 0.
Proof.
  intros m n d eq_mMn eq_SmMn.
  apply simplificationDroiteSoustractionNonNulle in eq_SmMn.
  simpl in eq_SmMn.
  injection eq_SmMn; intro eq_SmMn'.
  apply simplificationDroiteOpposeSoustractionNulle in eq_mMn.
  destruct eq_mMn as [d' eq_n].
  rewrite eq_SmMn' in eq_n.
  rewrite PeanoNat.Nat.add_assoc in eq_n.
  apply eq_sym in eq_n.
  apply simplificationDroiteAddition in eq_n.
  rewrite PeanoNat.Nat.sub_diag in eq_n.
  apply PeanoNat.Nat.eq_add_0 in eq_n.
  destruct eq_n as [eq_d' eq_d].
  split.
  {
    rewrite eq_d in eq_SmMn'.
    assumption.
  }
  {
    assumption.
  }
Qed.

Lemma opposeSoustractionNonNulle :
  forall m n d,
    m - n = S d -> n - m = 0.
Proof.  
  intros m n d H.
  apply simplificationDroiteSoustractionNonNulle in H.
  apply eq_sym in H.
  apply opposeSimplificationDroiteAddition in H.
  symmetry.
  assumption.
Qed.


Lemma suivantDiagonal :
  forall n, S n - n = 1.
Proof.
  intro n.
  symmetry.
  apply simplificationDroiteAddition.
  simpl.
  reflexivity.
Qed.

Lemma decalageDiagonal :
  forall d n, d + n - n = d.
Proof.
  intros d n.
  symmetry.
  apply simplificationDroiteAddition.
  reflexivity.
Qed.

Lemma successeurSoustractionNonNulle :
  forall m n d,
    m - n = S d -> S m - n = S (S d).
Proof.
  intros m n d H.
  symmetry.
  apply simplificationDroiteAddition.
  simpl.
  f_equal.
  transitivity (S d + n).
  reflexivity.
  symmetry.
  apply simplificationDroiteSoustractionNonNulle.
  assumption.
Qed.

Lemma predecesseurSoustractionNulle :
  forall m n,
    S m - n = 0 -> m - n = 0.
Proof.
  intros m n H.
  destruct (simplificationDroiteOpposeSoustractionNulle _ _ H) as [d eqD].
  apply opposeSoustractionNonNulle with d.
  symmetry.
  apply simplificationDroiteAddition.
  transitivity (d + S m).
  apply PeanoNat.Nat.add_succ_comm.
  symmetry.
  assumption.
Qed.
