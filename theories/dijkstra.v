Require Import tactics.
Require Import List Nat Bool egalite Omega.
Import ListNotations.

Local Open Scope eqb_scope.
Module NonPondéré.

Inductive At : Type :=
| G : nat -> nat -> At
| G' : nat -> nat -> At
| C : nat -> nat -> At
| T : nat -> nat -> At.

Definition g := fun a b => atome (G a b).
Definition g' := fun a b => atome (G' a b).
Definition t := fun a b => atome (T a b).
Definition c := fun a b => atome (C a b).

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1, T m2 n2 => (m1, n1) =? (m2, n2)
  | G m1 n1, G m2 n2 => (m1, n1) =? (m2, n2)
  | G' m1 n1, G' m2 n2 => (m1, n1) =? (m2, n2)
  | C m1 n1, C m2 n2 => (m1, n1) =? (m2, n2)
  | _, _            => false
  end.

Definition ArcsConsommes X := forall u v, Absence X (G u v).

Definition CandidatsConsommes X := forall u v, Absence X (C u v).

(* G(a, b) & T(a', a) & ¬T(?, b) & ¬C(?, b) -> G(a, b) & T(a', a) & C(a, b) *)

CoFixpoint Candidat :=
  (∀_m Y,
  ((ArcsConsommes Y \/ 
    (forall a b, Presence Y (G a b) -> forall a', Absence Y (T a' a)) \/
    (forall a b a', Presence Y (G a b) /\ Presence Y (T a' a)
        -> exists b', (Presence Y (T b' b) \/ Presence Y (C b' b)))
  ) ? Y -o Y))
  ∧
  (
  (∀_m X , ∀_v a , ∀_v b , ∀_v a',
          ((forall b', Absence (t a' a ⊗ X) (T b' b) /\ Absence X (C b' b))
             ? (g a b ⊗ t a' a ⊗ X)
                        -o (g' a b ⊗ t a' a ⊗ c a b ⊗ X))) ⊠ Candidat).

(* C(a,b) & ¬T(?, b) -> T(a,b) *)

CoFixpoint Recouvrement :=
  (∀_m Y,
    ((CandidatsConsommes Y \/ 
      (forall a b, Presence Y (C a b) -> exists b', Presence Y (T b' b))
    ) ? Y -o Y))
   ∧
   (
   (∀_m X , ∀_v a , ∀_v b,
            ((forall b', Absence X (T b' b))
            ? (c a b ⊗ X)
                -o (t a b ⊗ X))) ⊠ Recouvrement).

(** Tactics *)

(* Apply Candidat *)

Ltac Candidat a b a' :=
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a'); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

(* Apply Recouvrement *)

Ltac Recouvrement a b := 
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
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
                       repeat
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

Ltac ConclureRecouvrement := 
  try(simpl; intros);
  match goal with
   | H : _ \/ _ |- _ => destruct H; 
                                         [ tryif (discriminate H) then simpl
                                                                               else  injection H; intros; subst; eexists; 
                                                                                        intuition; reflexivity
                                          | ]; ConclureRecouvrement
   | H : _ = _ |- _       => tryif (discriminate H) then simpl
                                                                          else  injection H; intros; subst; eexists;
                                                                                   intuition; reflexivity
   end.

Ltac ConclureCandidat := idtac "Essayer la partie Gauche"; 
                                            tryif resoudreGauche then idtac "Succès !" else idtac "Échec";
                                            idtac "Essayer la partie Droite"; 
                                            tryif resoudreDroite then idtac "Succès !" else idtac "Échec".

Definition grapheSimple := g 1 2 ⊗ g 2 3 ⊗ g 1 3.

Definition ruleSet := [Candidat; Recouvrement].

(** Example *)

Theorem recouvrementSimple :
  Transformation ruleSet
                 (grapheSimple ⊗ t 1 1 ⊗ c 1 3 ⊗ c 2 3) (g' 1 2 ⊗ g 2 3 ⊗ g 1 3 ⊗ c 1 3 ⊗ t 1 1 ⊗ t 1 2 ⊗ t 2 3).
Proof.
  (* Generate C 1 2 *)
  dupliquerExponentielle 0.
  Candidat 1 2 1.

  (* Generate T 1 2 *)
  dupliquerExponentielle 1.
  Recouvrement 1 2.

  (* Generate T 2 3 *)
  dupliquerExponentielle 1.
  Recouvrement 2 3.
  ChoisirNeutrePartout.
  ConclureCandidat.
  ConclureRecouvrement.
Qed.

End NonPondéré.

Module Pondéré.

Inductive At : Type :=
| G : nat -> nat -> nat -> At
| C : nat -> nat -> nat -> At
| T : nat -> nat -> nat -> At.

Definition g := fun a b c => atome (G a b c).
Definition t := fun a b c => atome (T a b c).
Definition c := fun a b c => atome (C a b c).

(*
- G(a, b, n) : graphe décrit par la relation G contenant les arcs
- C(a, b, n) : table des candidats décrite par la relation C (b parent de a) à distance n
- T(a, b, n) : arbre couvrant décrit par la relation T (b parent de a) à distance n
 *)

(* G(a, b, n) & T(a', a, da) & ¬T(?, b, ?) & ¬C(?, b, ?) 
                                  -> G(a, b, n) & T(a', a, da) & C(a, b, da + n) *)

CoFixpoint Candidat1 :=
  (∀_m Y, (
  ((forall a b n, Absence Y (G a b n))
  \/ (forall a b n, Presence Y (G a b n) -> forall a' da, Absence Y (T a' a da)) 
  \/ (forall a b n a' da, Presence Y (G a b n) /\ Presence Y (T a' a da) 
                                    -> exists b' db, Presence Y (T b' b db) \/ Presence Y (C b' b db))) 
  ? Y -o Y ))
   ∧
  (
  (∀_m X , ∀_v a , ∀_v b , ∀_v n , ∀_v a' , ∀_v da,
          ((forall b1 b2, Absence (t a' a da ⊗ X) (T b1 b b2) /\ Absence X (C b1 b b2))
             ? (g a b n ⊗ t a' a da ⊗ X) -o (g a b n ⊗ t a' a da ⊗ c a b (da + n) ⊗ X))) ⊠ Candidat1).

(* G(a, b, n) & T(a', a, da) & ¬T(?, b, ?) & C(?, b, db) & (da + n < db) 
                                  -> G(a, b, n) & T(a', a, da) & C(a, b, da + n) *)

CoFixpoint Candidat2 :=
  (∀_m Y, (
  ((forall a b n, Absence Y (G a b n))
  \/ (forall a b n, Presence Y (G a b n) -> forall a' da, Absence Y (T a' a da)) 
  \/ (forall a b n a' da, Presence Y (G a b n) /\ Presence Y (T a' a da) 
                                    -> forall b' db, Absence Y (C b' b db))
  \/ (forall a b n a' da b' db, 
                                  Presence Y (G a b n) /\ Presence Y (T a' a da) /\ Presence Y (C b' b db)
                                  -> db <= da + n \/ exists b'' db'', Presence Y (T b'' b db'')))
  ? Y -o Y ))
   ∧
  (
  (∀_m X , ∀_v a , ∀_v b , ∀_v n , ∀_v a' , ∀_v da , ∀_v b' , ∀_v db,
      (((forall b1 b2, Absence (t a' a da ⊗ X) (T b1 b b2)) /\ (da + n < db) )
         ? (g a b n ⊗ t a' a da ⊗ c b' b db ⊗ X) -o (g a b n ⊗ t a' a da ⊗ c a b (da + n) ⊗ X))) ⊠ Candidat2).

(* C(a,b,db) & ¬T(?,b,?) -> T(a,b,db) *)

CoFixpoint Recouvrement :=
  (∀_m Y, (
  ((forall a b db, Absence Y (C a b db))
  \/ (forall a b db, Presence Y (C a b db) -> exists b' db, Presence Y (T b' b db))) 
  ? Y -o Y ))
  ∧
  (
  (∀_m X , ∀_v a , ∀_v b , ∀_v db,
        ((forall b1 b2, Absence X (T b1 b b2))
        ? (c a b db ⊗ X) -o (t a b db ⊗ X))) ⊠ Recouvrement).

Definition grapheSimple := g 1 2 1 ⊗ g 2 3 2 ⊗ g 1 3 4.

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1 p1, T m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | G m1 n1 p1, G m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | C m1 n1 p1, C m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | _, _            => false
  end.

(* Tactiques *)

Ltac Candidat1 a b n a' da := 
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 n); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a'); simpl; trivial; simpl;
  eapply (instanciationValeur 0 da); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

Ltac Candidat2 a b n a' da b' db :=
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

Ltac Recouvrement1 a b n :=
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 n); simpl; trivial; simpl;
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

Ltac ConclureCandidat1 := idtac "";
                          tryif resoudreGauche then idtac "Constraints solved : no candidate can be generated with those arcs."
                          else tryif resoudreDroite 
                          then idtac "Constraints solved : every arc has already generated a covered vertice or a current candidate."
                          else idtac "Cannot solve constraints".

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
                                        else injection H''; intros; subst; 
                                                tryif (left; omega) then simpl 
                                                                               else (do 2 eexists); intuition; reflexivity
                                        | ]; 
                                                DeterminerC2 H3' H''
  | _ = _      => tryif discriminate H''
                       then simpl
                       else injection H''; intros; subst; tryif (left; omega)
                                                                             then simpl 
                                                                             else (do 2 eexists); intuition; reflexivity
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
   right; right; simpl; intros;
   match goal with
   | H : ?H1 /\ ?H2 /\ ?H3 |- _ => destruct H as [?H [?H' ?H'']]; DeterminerG2 H1 H2 H3 H H' H''
   end.

Ltac ConclureCandidat2 := idtac "";
                          tryif resoudreGauche then idtac "Constraints solved : no candidate can be generated with those arcs." 
                          else tryif resoudreDroite then idtac "Constraints solved : every arc has already generated a covered vertice or a current candidate."
                          else tryif resoudreDroite2 then idtac "Constraints solved : every new generated candidate would have a bigger ponderation than in the current state"
                          else idtac "Cannot solve constraints".

Definition règles := [Candidat1; Candidat2; Recouvrement].

Theorem recouvrementSimple :
Transformation 
règles
(grapheSimple  ⊗ c 1 1 0) 
(grapheSimple ⊗ t 1 1 0 ⊗ t 1 2 1 ⊗ t 2 3 3).
 Proof.
 (* Generate T 1 1 0 : rule 2*)
  dupliquerExponentielle 2.
  Recouvrement1 1 1 0.

  (* Generate C 1 2 1 : test rule 0 *)
  dupliquerExponentielle 0.
  Candidat1 1 2 1 1 0.

  (* Generate T 1 2 1 *)
  dupliquerExponentielle 2.
  Recouvrement1 1 2 1.

  (* Generate C 1 3 4 *)
  dupliquerExponentielle 0.
  Candidat1 1 3 4 1 0.

  (* Replace it by C 2 3 3 : test rule 1 *)
  dupliquerExponentielle 1.
  Candidat2 2 3 2 1 1 1 4.

  (* Generate T 2 3 3*)
  dupliquerExponentielle 2.
  Recouvrement1 2 3 3.
  ChoisirNeutrePartout.
  ConclureCandidat1.
  ConclureCandidat2.
Qed.

(* Un exemple à 6 sommets :
    Graphe (1 est racine)


                                             ----------------------------------------
                                             |                                              |
                                             |                                             ⋁
                                             |            1 ---------  (4)  -------> 2 <----------
                                             |            / \                                                \
                                            (4)        /    \                                               |
                                             |        (1)     ---- (2) ----                              |
                                             |         /                       |                            (3)
                                             |        /                       ⋁                        |
                                             ----- 4 ------ (2) ------> 5 ---------(0)-------> 3
                                                     |                         |
                                                     |                       (1)
                                                     |                         |
                                                     |                        ⋁
                                                     --------(3)-------> 6






     Dois mener à l'arbre couvrant T suivant :

                                                        1 ----------- 2
                                                       /  \
                                                      /    \
                                                    4     5
                                                          /  \
                                                         /    \
                                                       6      3


*)

Definition graphe6Sommets := g 1 2 4 ⊗ g 1 4 1 ⊗ g 1 5 2 ⊗ g 4 5 2 ⊗ g 4 6 3 ⊗
                                                     g 5 6 1 ⊗ g 5 3 0 ⊗ g 3 2 3 ⊗ g 4 2 4.

Theorem Recouvrement6Sommets : 
  Transformation règles
                 (graphe6Sommets  ⊗ c 1 1 0) 
                 (graphe6Sommets ⊗ t 1 1 0 ⊗ t 1 2 4 ⊗ t 1 4 1 ⊗ t 1 5 2 ⊗ t 5 6 3 ⊗ t 5 3 2).
Proof.
  (* Generate T 1 1 0 : règle 2*)
  dupliquerExponentielle 2.
  Recouvrement1 1 1 0.

  (* Generate C 1 2 4 & C 1 4 1 : tester la structure de pile avec règle 0 *)
  dupliquerExponentielle 0.
  Candidat1 1 2 4 1 0.
  dupliquerExponentielle 0.
  Candidat1 1 4 1 1 0.

  (* Generate T 1 4 1 & T 1 2 4 *)
  dupliquerExponentielle 2.
  Recouvrement1 1 4 1.
  dupliquerExponentielle 2.
  Recouvrement1 1 2 4.

  (* Generate C 4 5 3 & replace it by C 1 5 2 : test règle 1 *)
  dupliquerExponentielle 0.
  Candidat1 4 5 2 1 1.
  dupliquerExponentielle 1.
  Candidat2 1 5 2 1 0 4 3.

  (* Generate T 1 5 2 *)
  dupliquerExponentielle 2.
  Recouvrement1 1 5 2.

  (* Generate C 5 6 3 & C 5 3 2 *)
  dupliquerExponentielle 0.
  Candidat1 5 6 1 1 2.
  dupliquerExponentielle 0.
  Candidat1 5 3 0 1 2.

  (* Generate  T 5 3 2 & T 5 6 3 *)
  dupliquerExponentielle 2.
  Recouvrement1 5 3 2.
  dupliquerExponentielle 2.
  Recouvrement1 5 6 3.
  ChoisirNeutrePartout.
  ConclureCandidat1.
  ConclureCandidat2.
Qed.



End Pondéré.
