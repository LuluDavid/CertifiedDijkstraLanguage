Require Export List.

Import ListNotations.

(** Structure *)

Definition AbsenceListe
           {A: Type}
  : list A -> A -> Prop.
  fix HR 1.
  intros M a.
  destruct M as [ | x l].
  {
    exact True.
  }
  {
    exact ((x <> a) /\ (HR l x)).
  }
Defined.

(* récriture en associant à droite (comme la notation) *)
Lemma recritureConcatenation :
  forall {T : Type},
  forall l1 l2 l3 : list T,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  apply app_assoc_reverse.
Qed.

Lemma eliminationListeVide :
  forall {T : Type},
  forall l : list T,
    l ++ nil = l.
Proof.
  apply app_nil_r.
Qed.

Ltac egaliteListes :=
  repeat (rewrite recritureConcatenation || rewrite eliminationListeVide || simpl); reflexivity.

Lemma testEgaliteListes :
  forall l1 l2 l3 l4 : list nat,
    l1 ++ [1 ; 2] ++ 3 :: l2 ++ l3 ++ nil ++ [4; 5; 6] ++ l4 ++ nil
    = (l1 ++ ([1 ; 2] ++ nil ++ 3 :: l2 ++ l3) ++ [4; 5; 6]) ++ l4 ++ nil.
Proof.
  intros.
  egaliteListes.
Qed.

Lemma simplificationSingleton :
  forall T : Type,
  forall k u l (v : T),
    k ++ [u] ++ l = [v] -> u = v /\ k = [] /\ l = [].
Proof.
  intro T.
  fix HR 1.
  intros k u l v eqL.
  destruct k as [ | tk rk].
  {
    simpl.
    simpl in eqL.
    injection eqL.
    intros eqLv eqUV.
    tauto.
  }
  {
    injection eqL.
    intros Absurde _.
    exfalso.
    destruct rk; discriminate Absurde.
  }
Qed.

Lemma longueurListeSingleton :
  forall T : Type,
  forall l : list T,
  forall e : T,
    length (l ++ [e]) = S (length l).
Proof.
  intros T l e.
  rewrite app_length.
  simpl.
  rewrite PeanoNat.Nat.add_comm.
  reflexivity.
Qed.

Lemma concatenationVide :
  forall A, forall (l1 l2 : list A),
    l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros A l1 l2.
  destruct l1.
  {
    simpl.
    auto.
  }
  {
    intro Abs.
    discriminate Abs.
  }
Qed.

Proposition teteFonctionnelle:
  forall A : Type,
  forall t1 t2 : A,
  forall l1 l2 : list A,
    t1 :: l1 = t2 :: l2 -> t1 = t2.
Proof.
  intros.
  injection H.
  intros; assumption.
Qed.