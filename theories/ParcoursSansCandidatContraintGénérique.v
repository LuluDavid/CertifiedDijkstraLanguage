Require Export TactiquesParcoursContraint.
Require Import List Nat Bool Omega.
Import ListNotations.
Require Import Coq.Program.Equality Coq.Logic.Classical_Pred_Type.

Local Open Scope eqb_scope.

Module NonPondéré.

(** Parcours sans candidat *)

Inductive At : Type :=
| G : nat -> nat -> At
| G' : nat -> nat -> At
| T : nat -> nat -> At.

Definition g := fun a b => atome (G a b).
Definition g' := fun a b => atome (G' a b).
Definition t := fun a b => atome (T a b).

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1, T m2 n2 => (m1, n1) =? (m2, n2)
  | G m1 n1, G m2 n2 => (m1, n1) =? (m2, n2)
  | G' m1 n1, G' m2 n2 => (m1, n1) =? (m2, n2)
  | _, _            => false
  end.

(*
- G(a, b) : graphe décrit par la relation G contenant les arcs
- T(a, b) : arbre couvrant décrit par la relation T, 
  correspondant à la table de routage (b de parent a)
 *)

(** Parcours de graphe *)

(* G(a, b) & T(a', a) & ¬T(?, b) -> G'(a, b) & T(a', a) & T(a, b) *)

Definition ArcsConsommes X := forall u v, Absence X (G u v).

Definition Recouvrement :=
  ∀_m X , ∀_v a , ∀_v b , ∀_v a',
     ((forall b', Absence (t a' a ⊗ X) (T b' b)) ? 
     (g a b ⊗ t a' a ⊗ X) -o (g' a b ⊗ t a' a ⊗ t a b ⊗ X)).

Definition RecouvrementGardé := exponentielDeterministe Recouvrement.

(** Tactics *)

(* Apply Recouvrement *)

Ltac Recouvrement a b a' :=
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a'); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

(** Example *)

Definition grapheSimple := g 1 2 ⊗ g 2 3 ⊗ g 1 3.

Theorem recouvrementSimple :
  Transformation [RecouvrementGardé]
                 (grapheSimple ⊗ t 1 1) (g' 1 2 ⊗ g' 2 3 ⊗ g 1 3 ⊗ t 1 1 ⊗ t 1 2 ⊗ t 2 3).
Proof.
  dupliquerExponentielle 0.
   Recouvrement 1 2 1.
   dupliquerExponentielle 0.
   Recouvrement 2 3 1.
   ChoisirNeutrePartout.
   unfold Recouvrement.
   simplBlocage.
   admit.
Admitted.





End NonPondéré.

Module Pondéré.

(** Parcours sans candidat pondéré *)

Inductive At : Type :=
| G : nat -> nat -> nat -> At
| T : nat -> nat -> nat -> At.

Definition g := fun a b n => atome (G a b n).
Definition t := fun a b n => atome (T a b n).

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1 p1, T m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | G m1 n1 p1, G m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | _, _            => false
  end.

(** Parcours de graphe *)

(* G(a, b, n) & T(a', a, da) & ¬T(?, b, ?) -> G(a, b, n) & T(a', a, da) & T(a, b, da + n)  *)

Definition Recouvrement1 :=
  ∀_m X , ∀_v a , ∀_v b , ∀_v n , ∀_v a' , ∀_v da,
          ((forall b' b'', Absence (t a' a da ⊗ X) (T b' b b''))
             ? (g a b n ⊗ t a' a da ⊗ X) -o (g a b n ⊗ t a' a da ⊗ t a b (da + n) ⊗ X)).

(* G(a, b, n) & T(a', a, da) & T(b', b, db) & (da + n < db)  -> G(a, b, n) & T(a', a, da) & T(a, b, da + n) *)

Definition Recouvrement2 :=
   ∀_m X, ∀_v a , ∀_v b , ∀_v n , ∀_v a' , ∀_v da , ∀_v b' , ∀_v db,
          (( da + n < db )
             ? (g a b n ⊗ t a' a da ⊗ t b' b db ⊗ X) -o (g a b n ⊗ t a' a da ⊗ t a b (da + n) ⊗ X)).

Definition Recouvrement1Gardé := exponentielDeterministe Recouvrement1.

Definition Recouvrement2Gardé := exponentielDeterministe Recouvrement2.

Definition grapheSimple := g 1 2 1 ⊗ g 2 3 2 ⊗ g 1 3 4.

(** Tactics *)

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


Definition règles := [Recouvrement1Gardé; Recouvrement2Gardé].

Theorem recouvrementSimple :
  Transformation règles
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
  ChoisirNeutrePartout; simplBlocage.
Admitted.

End Pondéré.

