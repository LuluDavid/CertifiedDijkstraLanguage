Require Export TactiquesParcours.
Require Import List Nat Omega.
Import ListNotations.
Require Import Coq.Program.Equality.

Local Open Scope eqb_scope.

Module NonPondéré.

(** Parcours sans candidat *)

Inductive At : Type :=
| G : nat -> nat -> At
| T : nat -> nat -> At.

Definition g := fun a b => atome (G a b).
Definition t := fun a b => atome (T a b).

(*
- G(a, b) : graphe décrit par la relation G contenant les arcs
- T(a, b) : arbre couvrant décrit par la relation T, 
  correspondant à la table de routage (b de parent a)
 *)

(** Parcours de graphe *)

(* G(a, b) & T(a', a) & ¬T(?, b) -> G(a, b) & T(a', a) & T(a, b) *)
Definition Recouvrement :=
  ∀_m X, ∀_v a, ∀_v b, ∀_v a',
          ((forall b', Absence (t a' a ⊗ X) (T b' b))
             ? (g a b ⊗ t a' a ⊗ X) -o (g a b ⊗ t a' a ⊗ t a b ⊗ X)).

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1, T m2 n2 => (m1, n1) =? (m2, n2)
  | G m1 n1, G m2 n2 => (m1, n1) =? (m2, n2)
  | _, _            => false
  end.

Definition grapheSimple := g 1 2 ⊗ g 2 3 ⊗ g 1 3.

(* Tactics *)

Ltac Recouvrement a b a' :=
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a'); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

Theorem recouvrementSimple :
  Transformation [exponentiel Recouvrement]
                 (grapheSimple ⊗ t 1 1) (grapheSimple ⊗ t 1 1 ⊗ t 1 2 ⊗ t 2 3).
Proof.
   dupliquerExponentielle 0.
   Recouvrement 1 2 1.
   dupliquerExponentielle 0.
   Recouvrement 2 3 1.
   Conclure.
Qed.

(* 
  Il faut montrer que cette propriété se conserve par application de toute règle :

  forall M: @Molecule (nat*nat), forall (a1 a2 b),
  In (a1, b) M -> In (a2, b) M -> a1 = a2
*)

Definition UniciteParent M := forall (a1 a2 b : nat), Presence M (T a1 b) -> Presence M (T a2 b) -> a1 = a2.

Lemma UniciteParentEquivalence : forall M1 M2, 
                                                              UniciteParent M1 -> EquivalenceMoleculaire [M1] M2 -> UniciteParent M2.
Proof.
Admitted.

Lemma UniciteParentConservee : forall M1 M2 R, 
  Transformation R M1 M2 -> R = [Recouvrement] -> UniciteParent M1 -> UniciteParent M2.
Proof.
  intros M1 M2 R H.
  induction H; intros; subst;
  try(destruct n; simpl in *; discriminate H); 
  try (discriminate H1).
  - destruct n; simpl in *; try discriminate H.
    injection H as H; subst.
    clear IHTransformation.
    remember [∀1 (fun a : nat =>
                    ∀1 (fun b : nat =>
                    ∀1 (fun a' : nat =>
                        (forall b' : nat, T b' b <> T a' a /\ Absence X (T b' b)) ? g a b ⊗ t a' a ⊗ X --o
                        g a b ⊗ t a' a ⊗ t a b ⊗ X, neutreRegle)))] 
                        as R.
    revert HeqR H2.
    induction H0; intros; subst; 
    try(destruct n; simpl in *; discriminate H); 
    try (discriminate HeqR).
    -- destruct n; simpl in *; try discriminate H.
        injection H as H; subst.
        clear IHTransformation.
        simpl_existT; subst.
        remember [∀1 (fun b : nat =>
                       ∀1 (fun a' : nat =>
                            (forall b' : nat, T b' b <> T a' v /\ Absence X (T b' b)) ? g v b ⊗ t a' v ⊗ X --o
                            g v b ⊗ t a' v ⊗ t v b ⊗ X, neutreRegle))] 
                            as R.
        revert HeqR H2.
        induction H0; intros; subst; 
        try(destruct n; simpl in *; discriminate H); 
        try (discriminate HeqR).
        --- destruct n; simpl in *; try discriminate H.
            injection H as H; subst.
            clear IHTransformation.
            simpl_existT; subst.
            remember [∀1 (fun a' : nat =>
                                (forall b' : nat, T b' v0 <> T a' v /\ Absence X (T b' v0)) ? g v v0 ⊗ t a' v ⊗ X --o
                                g v v0 ⊗ t a' v ⊗ t v v0 ⊗ X, neutreRegle)] 
                                as R.
             revert HeqR H2.
             induction H0; intros; subst; 
             try(destruct n; simpl in *; discriminate H); 
             try (discriminate HeqR).
             + destruct n; simpl in *; try discriminate H.
                injection H as H; subst.
                clear IHTransformation.
                simpl_existT; subst.
                remember [(forall b' : nat, T b' v0 <> T v1 v /\ Absence X (T b' v0)) ? g v v0 ⊗ t v1 v ⊗ X --o
                                    g v v0 ⊗ t v1 v ⊗ t v v0 ⊗ X, neutreRegle] 
                                as R.
                 revert HeqR H2.
                 induction H0; intros; subst; 
                 try(destruct n; simpl in *; discriminate H); 
                 try (discriminate HeqR).
                 ++ destruct n; simpl in *; try discriminate H.
                      injection H as H; subst.
                      apply TransformationNeutre in H0_0.
                      apply solutionInerte in H0_.
                      apply solutionInerte in H0_0.
                      clear IHTransformation1 IHTransformation2.
                      apply (UniciteParentEquivalence _ (g v v0 ⊗ t v1 v ⊗ X)) in H2; trivial.
                      clear H0_.
                      assert (UniciteParent (g v v0 ⊗ t v1 v ⊗ t v v0 ⊗ X)).
                      {
                      clear H0_0.
                      rename H0 into H1.
                      unfold UniciteParent in *; intros.
                      simpl in *.
                      destruct H.
                      - destruct H.
                        -- destruct H.
                          --- discriminate H.
                          --- injection H; intros.
                              destruct H0.
                              + destruct H0.
                                ++ destruct H0.
                                  +++ discriminate H0.
                                  +++ injection H0; intros; subst; reflexivity.
                                ++ injection H0; intros; subst.
                                     destruct (H1 v1); destruct H3; reflexivity.
                              + apply (H2 _ _ b).
                                ++ left; right; assumption.
                                ++ right; assumption.
                        -- injection H; intros.
                           destruct H0.
                           --- destruct H0.
                              + destruct H0.
                                ++ discriminate H0.
                                ++ injection H0; intros; subst.
                                     destruct (H1 v1); destruct H3; reflexivity.
                              + injection H0; intros; subst; reflexivity.
                           --- subst.
                                destruct (H1 a2).
                                apply AbsenceNotPresence in H4.
                                destruct H4; assumption.
                      - destruct H0.
                        -- destruct H0.
                          --- destruct H0.
                            + discriminate H0.
                            + apply (H2 _ _ b).
                               ++ right; assumption.
                               ++ left; right; assumption.
                          --- injection H0; intros; clear H0; subst.
                              destruct (H1 a1).
                              apply AbsenceNotPresence in H3.
                              destruct H3; assumption.
                        -- apply (H2 _ _ b); right; assumption.
                    }
                    apply (UniciteParentEquivalence _ M2) in H; trivial.
                 ++ destruct n; simpl in *; try discriminate H.
                      injection H as H; subst.
                      apply IHTransformation; trivial.
                 ++ destruct n; simpl in *.
                      +++  apply solutionInerte in H0_. apply (UniciteParentEquivalence _ N) in H2; trivial.
                              apply IHTransformation2; trivial.
                      +++  apply solutionInerte in H0_0.
                              apply (UniciteParentEquivalence N); trivial. 
                              apply IHTransformation1; trivial.
             + destruct n; simpl in *; try discriminate H.
                injection H as H; subst.
                apply IHTransformation; trivial.
              + destruct n; simpl in *.
                ++ apply solutionInerte in H0_. apply (UniciteParentEquivalence _ N) in H2; trivial.
                    apply IHTransformation2; trivial.
                ++ apply solutionInerte in H0_0.
                    apply (UniciteParentEquivalence N); trivial. 
                    apply IHTransformation1; trivial.
        --- destruct n; simpl in *; try discriminate H.
             injection H as H; subst.
             apply IHTransformation; trivial.
        --- destruct n; simpl in *.
            + apply solutionInerte in H0_. apply (UniciteParentEquivalence _ N) in H2; trivial.
                apply IHTransformation2; trivial.
            + apply solutionInerte in H0_0.
                apply (UniciteParentEquivalence N); trivial. 
                apply IHTransformation1; trivial.
    -- destruct n; simpl in *; try discriminate H.
       injection H as H; subst.
       apply IHTransformation; trivial.
    -- destruct n; simpl in *.
      --- apply solutionInerte in H0_. apply (UniciteParentEquivalence _ N) in H2; trivial.
          apply IHTransformation2; trivial.
      --- apply solutionInerte in H0_0.
          apply (UniciteParentEquivalence N); trivial. 
          apply IHTransformation1; trivial.
  - destruct n; simpl in *; try discriminate H.
    injection H as H; subst.
    apply IHTransformation; trivial.
  - destruct n; simpl in *.
    -- apply solutionInerte in H. apply (UniciteParentEquivalence _ N) in H2; trivial.
       apply IHTransformation2; trivial.
    -- apply solutionInerte in H0.
       apply (UniciteParentEquivalence N); trivial. 
       apply IHTransformation1; trivial.
Qed.

End NonPondéré.



Module Pondéré.

(** Parcours sans candidat pondéré *)

Inductive At : Type :=
| G : nat -> nat -> nat -> At
| T : nat -> nat -> nat -> At.

Definition g := fun a b n => atome (G a b n).
Definition t := fun a b n => atome (T a b n).

(** Parcours de graphe *)

(* G(a, b, n) & T(a', a, da) & ¬T(?, b, ?) -> G(a, b, n) & T(a', a, da) & T(a, b, da + n) *)
Definition Recouvrement1:=
  ∀_m X, ∀_v a, ∀_v b, ∀_v n, ∀_v a', ∀_v da,
          ((forall b' b'', Absence (t a' a da ⊗ X) (T b' b b''))
             ? (g a b n ⊗ t a' a da ⊗ X) -o (g a b n ⊗ t a' a da ⊗ t a b (da + n) ⊗ X)).

(* G(a, b, n) & T(a', a, da) & T(b', b, db) & (da + n < db)  -> G(a, b, n) & T(a', a, da) & T(a, b, da + n) *)

Definition Recouvrement2 :=
  ∀_m X, ∀_v a, ∀_v b, ∀_v n, ∀_v a', ∀_v da, ∀_v b', ∀_v db,
            (( da + n < db )
             ? (g a b n ⊗ t a' a da ⊗ t b' b db ⊗ X) -o (g a b n ⊗ t a' a da ⊗ t a b (da + n) ⊗ X)).

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1 p1, T m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | G m1 n1 p1, G m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | _, _            => false
  end.

Definition grapheSimple := g 1 2 1 ⊗ g 2 3 2 ⊗ g 1 3 4.

(* Tactiques propres *)

Ltac Recouvrement1 a b n a' da :=
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 n); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a'); simpl; trivial; simpl;
  eapply (instanciationValeur 0 da); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

Ltac Recouvrement2 a b n a' da b' db:=
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 n); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a'); simpl; trivial; simpl;
  eapply (instanciationValeur 0 da); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b'); simpl; trivial; simpl;
  eapply (instanciationValeur 0 db); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

Theorem recouvrementSimple :
  Transformation [exponentiel Recouvrement1; exponentiel Recouvrement2]
                 (grapheSimple ⊗ t 1 1 0) (grapheSimple ⊗ t 1 1 0 ⊗ t 1 2 1 ⊗ t 2 3 3).
Proof.

  (* Generate t 1 2 1 *)
  dupliquerExponentielle 0.
  Recouvrement1 1 2 1 1 0.

  (* Generate t 1 3 4 *)
  dupliquerExponentielle 0.
  Recouvrement1 1 3 4 1 0.

  (* Generate t 2 3 3 *)
  dupliquerExponentielle 1.
  Recouvrement2 2 3 2 1 1 1 4.
  Conclure.
Qed.

End Pondéré.









