Require Export TactiquesParcoursContraint.
Require Import List Nat Bool Omega.
Import ListNotations.
Require Import Coq.Program.Equality.

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

CoFixpoint Recouvrement :=
  (∀_m Y,
  ((ArcsConsommes Y \/
    (forall a b, Presence Y (G a b) -> forall a', Absence Y (T a' a)) \/
    (forall a b a', Presence Y (G a b) /\ Presence Y (T a' a) -> exists b', (Presence Y (T b' b)))
    )
    ? Y -o Y)
  )
  ∧
  (
  (∀_m X , ∀_v a , ∀_v b , ∀_v a',
     ((forall b', Absence (t a' a ⊗ X) (T b' b)) ? 
     (g a b ⊗ t a' a ⊗ X) -o (g' a b ⊗ t a' a ⊗ t a b ⊗ X))) ⊠ Recouvrement).



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

Ltac resoudreGauche := 
  try(left; simpl; intros);
  match goal with
   | H : ?H1 \/ ?H2 |- _ => destruct H; 
                                         [ tryif (discriminate H) then simpl
                                                                               else  injection H; intros; subst; 
                                                                                        repeat (split; try discriminate); reflexivity
                                          | ]; resoudreGauche
   | H : _ = _ |- _       => tryif (discriminate H) then simpl
                                                                          else  injection H; intros; subst; 
                                                                                   repeat (split; try discriminate); reflexivity
   end.

Ltac DeterminerT H2 H0 :=
  match H2 with
  | _ \/ ?H2' => destruct H0; [tryif discriminate H0 
                                        then simpl
                                        else injection H0; intros; subst; 
                                                eexists; intuition; reflexivity
                                        |]; DeterminerT H2' H0
  | _       => tryif discriminate H0
                 then simpl
                 else injection H0; intros; subst; eexists; 
                         intuition; reflexivity
  end.

Ltac DeterminerG H1 H2 H H0 :=
  match H1 with
  | _ \/ ?H1' => destruct H; [tryif discriminate H 
                                    then simpl
                                    else injection H; intros; subst;
                                            DeterminerT H2 H0
                                    |]; DeterminerG H1' H2 H H0
  | _       => tryif discriminate H
               then simpl
               else injection H; intros; subst;
                       DeterminerT H2 H0
               | _       =>  tryif discriminate H0
                                then simpl
                                else injection H0; intros; subst; eexists; intuition; reflexivity
    end.

Ltac resoudreDroite :=
   right; simpl; intros;
   match goal with
   | H : ?H1 /\ ?H2 |- _ => destruct H as [?H ?H0]; 
                                         DeterminerG H1 H2 H H0
   end.

Ltac Conclure := idtac "Essayer la partie Gauche"; 
                              tryif resoudreGauche then idtac "Succès !" else idtac "Échec";
                              idtac "Essayer la partie Droite"; 
                              tryif resoudreDroite then idtac "Succès !" else idtac "Échec".

(** Example *)

Definition grapheSimple := g 1 2 ⊗ g 2 3 ⊗ g 1 3.

Theorem recouvrementSimple :
  Transformation [Recouvrement]
                 (grapheSimple ⊗ t 1 1) (g' 1 2 ⊗ g' 2 3 ⊗ g 1 3 ⊗ t 1 1 ⊗ t 1 2 ⊗ t 2 3).
Proof.
  dupliquerExponentielle 0.
   Recouvrement 1 2 1.
   dupliquerExponentielle 0.
   Recouvrement 2 3 1.
   ChoisirNeutrePartout.
   Conclure.
Qed.

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

CoFixpoint Recouvrement1 :=
  (∀_m Y, (
  ((forall a b n, Absence Y (G a b n))
  \/ (forall a b n, Presence Y (G a b n) -> forall a' da, Absence Y (T a' a da)) 
  \/ (forall a b n a' da, Presence Y (G a b n) /\ Presence Y (T a' a da) -> exists b' db, Presence Y (T b' b db))) 
  ? Y -o Y ))
   ∧
   (
   (∀_m X , ∀_v a , ∀_v b , ∀_v n , ∀_v a' , ∀_v da,
          ((forall b' b'', Absence (t a' a da ⊗ X) (T b' b b''))
             ? (g a b n ⊗ t a' a da ⊗ X) -o (g a b n ⊗ t a' a da ⊗ t a b (da + n) ⊗ X))) ⊠ Recouvrement1).

(* G(a, b, n) & T(a', a, da) & T(b', b, db) & (da + n < db)  -> G(a, b, n) & T(a', a, da) & T(a, b, da + n) *)

CoFixpoint Recouvrement2 :=
   (∀_m Y, (
   ((forall a b n, Absence Y (G a b n))
    \/ (forall a b n, Presence Y (G a b n) -> forall a' da b' db, Absence Y (T a' a da) \/ Absence Y (T b' b db))
    \/ (forall a b n a' da b' db, Presence Y (G a b n) /\ Presence Y (T a' a da) /\ Presence Y (T b' b db)
                                               -> db <= (da + n))
    )
   ? Y -o Y ))
   ∧
   (
   (∀_m X, ∀_v a , ∀_v b , ∀_v n , ∀_v a' , ∀_v da , ∀_v b' , ∀_v db,
          (( da + n < db )
             ? (g a b n ⊗ t a' a da ⊗ t b' b db ⊗ X) -o (g a b n ⊗ t a' a da ⊗ t a b (da + n) ⊗ X))) ⊠ Recouvrement2).

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

Ltac resoudreGauche := 
  try(left; simpl; intros);
  match goal with
   | H : ?H1 \/ ?H2 |- _ => destruct H; 
                                         [ tryif (discriminate H) then simpl
                                                                               else  injection H; intros; subst; 
                                                                                        repeat (split; try discriminate); reflexivity
                                          | ]; resoudreGauche
   | H : _ = _ |- _       => tryif (discriminate H) then simpl
                                                                          else  injection H; intros; subst; 
                                                                                   repeat (split; try discriminate); reflexivity
   end.

Ltac DeterminerT H2 H0 :=
  match H2 with
  | _ \/ ?H2' => destruct H0; [tryif discriminate H0 
                                        then simpl
                                        else injection H0; intros; subst; 
                                                do 2 eexists; intuition; reflexivity
                                        |]; DeterminerT H2' H0
  | _       => tryif discriminate H0
                 then simpl
                 else injection H0; intros; subst; do 2 eexists; 
                         intuition; reflexivity
  end.

Ltac DeterminerG H1 H2 H H0 :=
  match H1 with
  | _ \/ ?H1' => destruct H; [tryif discriminate H 
                                    then simpl
                                    else injection H; intros; subst;
                                            DeterminerT H2 H0
                                    |]; DeterminerG H1' H2 H H0
  | _       => tryif discriminate H
               then simpl
               else injection H; intros; subst;
                       DeterminerT H2 H0
               | _       =>  tryif discriminate H0
                                then simpl
                                else injection H0; intros; subst; eexists; intuition; reflexivity
    end.

Ltac resoudreDroite :=
   right; simpl; intros;
   match goal with
   | H : ?H1 /\ ?H2 |- _ => destruct H as [?H ?H0]; 
                                         DeterminerG H1 H2 H H0
   end.

Ltac ConclureRecouvrement1 := idtac "Essayer la partie Gauche"; 
                                                        tryif resoudreGauche then idtac "Succès !" else idtac "Échec";
                                                        idtac "Essayer la partie Droite"; 
                                                        tryif resoudreDroite then idtac "Succès !" else idtac "Échec".

Ltac resoudreGauche2 :=
  left; simpl; intros;
  repeat(
  match goal with
  | H : _ \/ _ |- _ => destruct H; [ tryif discriminate H then injection H; intros; subst;
                                                    try (left; repeat (split; discriminate); reflexivity); 
                                                    right; repeat (split; discriminate); reflexivity
                                                    else simpl | ]
  | H : _ = _ |- _ => tryif discriminate H then injection H; intros; subst;
                              try (left; repeat (split; discriminate); reflexivity); 
                              right; repeat (split; discriminate); reflexivity
                              else simpl
  end); reflexivity.

Ltac DeterminerC2 H3 H'' :=
  match H3 with
  | _ \/ ?H3' => destruct H'' as [H'' | H'']; 
                                        [tryif discriminate H'' 
                                        then simpl
                                        else injection H''; intros; subst; omega | ]; 
                                                DeterminerC2 H3' H''
  | _ = _      => tryif discriminate H''
                       then simpl
                       else injection H''; intros; subst; omega
  end.

Ltac DeterminerT2 H2 H3 H' H'' :=
  match H2 with
  | _ \/ ?H2' => destruct H' as [H'|  H']; 
                        [ tryif discriminate H' then simpl else injection H'; intros; subst; simpl;
                        DeterminerC2 H3 H''| ]; DeterminerT2 H2' H3 H' H''
  | _ = _    => tryif discriminate H'
                     then simpl
                     else injection H'; intros; subst; DeterminerC2 H3 H''
  end.

Ltac DeterminerG2 H1 H2 H3 H H' H'' :=
   match H1 with
   | _ \/ ?H1' => destruct H; [tryif discriminate H
                                              then simpl
                                              else injection H; intros; subst;
                                                      DeterminerT2 H2 H3 H' H'' | ]; 
                                                      DeterminerG2 H1' H2 H3 H H' H''
   |  _ =_ => tryif discriminate H
                   then simpl
                   else injection H; intros; subst;
                            DeterminerT2 H2 H3 H' H''
   end.

Ltac resoudreDroite2 :=
   right; simpl; intros;
   match goal with
   | H : ?H1 /\ ?H2 /\ ?H3 |- _ => destruct H as [?H [?H' ?H'']]; DeterminerG2 H1 H2 H3 H H' H''
   end.

Ltac ConclureRecouvrement2 := idtac "Essayer la partie Gauche"; 
                                                        tryif resoudreGauche2 then idtac "Succès !" else idtac "Échec";
                                                        idtac "Essayer la partie Droite"; 
                                                        tryif resoudreDroite2 then idtac "Succès !" else idtac "Échec".

Theorem recouvrementSimple :
  Transformation [Recouvrement1; Recouvrement2]
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
  ChoisirNeutrePartout.
  ConclureRecouvrement1.
  ConclureRecouvrement2.
Qed.

End Pondéré.

