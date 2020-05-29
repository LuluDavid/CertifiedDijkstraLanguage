Require Import TactiquesParcoursContraint.
Require Import List Nat Bool Egalite Omega.
Import ListNotations.

Local Open Scope eqb_scope.

(* Structure de données de la table des candidats *)

Definition structure {A:Type} : Type := list A.

(* Définition générique de push et pop *)

Definition push{A:Type} : Type := A -> list A -> list A.
Definition pop{A:Type} : Type := list A -> option (A * list A).

(* Définition pour une pile *)

Definition push_pile{A:Type} := @cons A.
Definition pop_pile{A:Type} (l:@list A) :=
  match l with
  | []       => None
  | x::l'   => Some (x, l')
  end. 

(* Définition pour une file *)

Definition push_file{A:Type}(x:A)(l:@list A) := l ++ [x].
Definition pop_file{A:Type} (l:@list A) :=
  match l with
  | []       => None
  | x::l'   => Some (x, l')
  end. 

Module NonPondéré.

Inductive At : Type :=
| G : nat -> nat -> At
| G' : nat -> nat -> At
| C : @structure (nat*nat) -> At
| T : nat -> nat -> At.

Definition g := fun a b => atome (G a b).
Definition g' := fun a b => atome (G' a b).
Definition t := fun a b => atome (T a b).
Definition c := fun s => atome (C s).

Definition ArcsConsommes X := forall u v, Absence X (G u v).

Definition CandidatsConsommes X := forall s, Presence X (C s) -> s = [].

(* G(a, b) & T(a', a) & ¬T(?, b) & ¬C(?, b) -> G(a, b) & T(a', a) & C(a, b) *)

CoFixpoint Candidat push :=
  (∀_m Y,
  ((ArcsConsommes Y \/ 
    (forall a b, Presence Y (G a b) -> forall a', Absence Y (T a' a)) \/
    (forall a b a' s, Presence Y (G a b) /\ Presence Y (T a' a) /\ Presence Y (C s)
        -> exists b', (Presence Y (T b' b) \/ In (b',b) s))
  ) ? Y -o Y))
  ∧
  (
  (∀_v s, ∀_m X , ∀_v a , ∀_v b , ∀_v a',
          ((forall b', Absence (t a' a ⊗ X) (T b' b) /\ AbsenceListe s (b', b))
             ? (g a b ⊗ t a' a ⊗ c s ⊗ X) 
                        -o (g' a b ⊗ t a' a ⊗ c (push (a, b) s) ⊗ X))) ⊠ (Candidat push)).

(* C(a,b) & ¬T(?, b) -> T(a,b) *)

CoFixpoint Recouvrement pop :=
  (∀_m Y,
  ((CandidatsConsommes Y \/ (forall s a b, Presence Y (C s) /\ In (a,b) s -> exists b', (Presence Y (T b' b)))
  ) ? Y -o Y))
  ∧
  (
  (∀_v s, ∀_v s', ∀_m X , ∀_v a , ∀_v b,
            (((forall b', Absence X (T b' b)) /\ (pop s = Some((a,b),s')))
            ? (c s ⊗ X)
                -o (c s' ⊗ t a b ⊗ X))) ⊠ (Recouvrement pop)).

(* En pratique, la condition d'arrêt à droite n'est jamais vérifiée si on démarre avec la racine comme candidat *)

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1, T m2 n2 => (m1, n1) =? (m2, n2)
  | G m1 n1, G m2 n2 => (m1, n1) =? (m2, n2)
  | G' m1 n1, G' m2 n2 => (m1, n1) =? (m2, n2)
  | C s1, C s2 => s1 =? s2
  | _, _            => false
  end.

(** Tactics *)

Ltac instancierListe M :=
  match M with
  | ?M1 ⊗ ?M2 =>
    match M1 with
    | c ?l => eapply (instanciationValeur 0 l); simpl; trivial; simpl
    | _     => match M2 with
                  | c ?l => eapply (instanciationValeur 0 l); simpl; trivial; simpl
                  | _ => try (instancierListe M1); try (instancierListe M2)
                  end
    end
  end.

(* Apply Candidat *)

Ltac Candidat a b a' :=
  match goal with
  | |- Transformation _?M _ => instancierListe M
  end;
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a'); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

(* Apply Recouvrement *)

Ltac Recouvrement a b :=
  match goal with
  | |- Transformation _?M _ => instancierListe M
  end;
  eapply (instanciationValeur 0); simpl; trivial; simpl;
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

Ltac ResoudreGauche := 
  try(left; simpl; intros);
  match goal with
   | H : ?H1 \/ ?H2 |- _ => destruct H; 
                                         [ tryif (discriminate H) then simpl
                                                                               else  injection H; intros; subst; 
                                                                                        repeat (split; try discriminate); reflexivity
                                          | ]; ResoudreGauche
   | H : _ = _ |- _       => tryif (discriminate H) then simpl
                                                                          else  injection H; intros; subst; 
                                                                                   repeat (split; try discriminate); reflexivity
   end.

Ltac DeterminerC H3 H'' :=
  match H3 with
  | _ \/ ?H3' => destruct H'' as [H'' | H'']; 
                                        [tryif discriminate H'' 
                                        then simpl
                                        else injection H''; intros; subst; 
                                                eexists; intuition; reflexivity | ]; 
                                                DeterminerC H3' H''
  | _ = _      => tryif discriminate H''
                       then simpl
                       else injection H''; intros; subst; eexists; 
                               intuition; reflexivity
  end.

Ltac DeterminerT H2 H3 H' H'' :=
  match H2 with
  | _ \/ ?H2' => destruct H' as [H'|  H']; 
                        [ tryif discriminate H' then simpl else injection H'; intros; subst; simpl;
                        DeterminerC H3 H''| ]; DeterminerT H2' H3 H' H''
  | _ = _    => tryif discriminate H'
                     then simpl
                     else injection H'; intros; subst; DeterminerC H3 H''
  end.

Ltac DeterminerG H1 H2 H3 H H' H'' :=
   match H1 with
   | _ \/ ?H1' => destruct H; [tryif discriminate H
                                              then simpl
                                              else injection H; intros; subst;
                                                      DeterminerT H2 H3 H' H'' | ]; 
                                                      DeterminerG H1' H2 H3 H H' H''
   |  _ =_ => tryif discriminate H
                   then simpl
                   else injection H; intros; subst;
                            DeterminerT H2 H3 H' H''
   end.

Ltac ResoudreDroite :=
   right; simpl; intros;
   match goal with
   | H : ?H1 /\ ?H2 /\ ?H3 |- _ => destruct H as [?H [?H' ?H'']]; DeterminerG H1 H2 H3 H H' H''
   end.

Ltac ConclureRecouvrement := 
  simpl; intros;
    match goal with
   | H : _ /\ _ |- _ => destruct H
   end;
   repeat (
   match goal with
   | H : _ \/ _ |- _ => destruct H; 
                               [ tryif (discriminate H) then simpl
                                                                     else  injection H; intros; subst; simpl in *;
                                                                              repeat (
                                                                              match goal with
                                                                              | H0 : _ \/ _ |- _ =>  destruct H0;
                                                                                                             [ tryif (discriminate H0) then simpl
                                                                                                               else  injection H0; intros; subst;
                                                                                                               eexists; intuition | ]
                                                                              | _ => try contradiction
                                                                              end)
                                 | ]
   | H : _ = _ |- _ => tryif (discriminate H) then simpl
                                                                   else  injection H; intros; subst; simpl in *;
                                                                            repeat (
                                                                            match goal with
                                                                            | H0 : _ \/ _ |- _ =>  destruct H0; [ tryif (discriminate H0) then simpl
                                                                                                                                    else  injection H0; intros; subst;
                                                                                                                                    eexists; intuition | ]
                                                                            | _                     => try contradiction
                                                                            end)
   end).

Ltac ConclureCandidat := idtac "Essayer la partie Gauche"; 
                                            tryif ResoudreGauche then idtac "Succès !" else idtac "Échec";
                                            idtac "Essayer la partie Droite"; 
                                            tryif ResoudreDroite then idtac "Succès !" else idtac "Échec".

(** Example *)

Definition grapheSimple := g 1 2 ⊗ g 2 3 ⊗ g 1 3.

Definition règles push pop := [Candidat push; Recouvrement pop].

Theorem recouvrementSimple :
  Transformation (règles push_pile pop_pile)
                 (grapheSimple ⊗ t 1 1 ⊗ c[(2,3);(1,3)]) (g' 1 2 ⊗ g 2 3 ⊗ g 1 3 ⊗ c[(1,3)] ⊗ t 1 1 ⊗ t 1 2 ⊗ t 2 3).
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
| C : @structure (nat*nat*nat) -> At
| T : nat -> nat -> nat -> At.

Definition g := fun a b c => atome (G a b c).
Definition t := fun a b c => atome (T a b c).
Definition c := fun s => atome (C s).

(*
- G(a, b) : graphe décrit par la relation G contenant les arcs
- C = [(a1,b1) ... (an, bn)] : table des candidats avec une structure sous-jacente de file/pile
- T(a, b) : arbre couvrant décrit par la relation T (b parent de a)
 *)

(* G(a, b, n) & T(a', a, da) & ¬T(?, b, ?) & ¬C(?, b, ?) 
                                  -> G(a, b, n) & T(a', a, da) & C(a, b, da + n) *)

CoFixpoint Candidat1 push :=
  (∀_m Y, (
  ((forall a b n, Absence Y (G a b n))
  \/ (forall s, Absence Y (C s))
  \/ (forall a b n, Presence Y (G a b n) -> forall a' da, Absence Y (T a' a da))
  \/ (forall a b n a' da s, Presence Y (G a b n) /\ Presence Y (T a' a da) /\ Presence Y (C s)
                                    -> exists b' db, Presence Y (T b' b db) \/ In (b', b, db) s))
  ? Y -o Y ))
   ∧
   (
  (∀_v s, ∀_m X , ∀_v a , ∀_v b , ∀_v n , ∀_v a' , ∀_v da,
          ((forall b1 b2, Absence (t a' a da ⊗ X) (T b1 b b2) /\ AbsenceListe s (b1, b, b2))
             ? (g a b n ⊗ t a' a da ⊗ c s ⊗ X) -o (g a b n ⊗ t a' a da ⊗ c (push (a, b, da + n) s) ⊗ X)))
             ⊠ Candidat1 push).

(* G(a, b, n) & T(a', a, da) & ¬T(?, b, ?) & C(?, b, db) & (da + n < db) 
                                  -> G(a, b, n) & T(a', a, da) & C(a, b, da + n) *)

CoFixpoint Candidat2 push :=
  (∀_m Y, (
  ((forall a b n, Absence Y (G a b n))
  \/ (forall s, Absence Y (C s))
  \/ (forall a b n, Presence Y (G a b n) -> forall a' da, Absence Y (T a' a da))
  \/ (forall a b n a' da s, Presence Y (G a b n) /\ Presence Y (T a' a da) /\ Presence Y (C s)
                                    -> forall b' db, AbsenceListe s (b', b, db) \/ (In (b', b, db) s -> db <= da + n)))
  ? Y -o Y ))
   ∧
  (
  (∀_v s, ∀_m X , ∀_v a , ∀_v b , ∀_v n,
  ∀_v a', ∀_v da , ∀_v b' , ∀_v db, 
          (((forall b1 b2, Absence (t a' a da ⊗ X) (T b1 b b2)) /\ In (b', b, db) s /\ (da + n < db) )
             ? (g a b n ⊗ t a' a da ⊗ c s ⊗ X) -o (g a b n ⊗ t a' a da ⊗ c (replace (b', b, db) (a, b, da + n) s push) ⊗ X)))
             ⊠ Candidat2 push).

(* C(a,b,db) & ¬T(?,b,?) -> T(a,b,db) *)

CoFixpoint Recouvrement pop :=
  (∀_m Y, (
  ((forall s, Absence Y (C s) \/ (Presence Y (C s) -> s = []))
  \/ (forall s a b db, Presence Y (C s) /\ In (a, b, db) s -> exists b' db, Presence Y (T b' b db)))
  ? Y -o Y ))
   ∧
  (
  (∀_v s, ∀_v s', ∀_m X , ∀_v a , ∀_v b , ∀_v db,
        (((forall b1 b2, Absence X (T b1 b b2)) /\ (pop s = Some ((a,b,db),s')) )
        ? (c s ⊗ X) -o (c s' ⊗ t a b db ⊗ X))) ⊠ Recouvrement pop).

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1 p1, T m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | G m1 n1 p1, G m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | C s1, C s2 => s1 =? s2
  | _, _            => false
  end.

(** Tactics *)

Ltac instancierListe M :=
  match M with
  | ?M1 ⊗ ?M2 =>
    match M1 with
    | c ?l => eapply (instanciationValeur 0 l); simpl; trivial; simpl
    | _     => match M2 with
                  | c ?l => eapply (instanciationValeur 0 l); simpl; trivial; simpl
                  | _ => try (instancierListe M1); try (instancierListe M2)
                  end
    end
  end.

Ltac Candidat1 a b n a' da := 
  match goal with
  | |- Transformation _?M _ => instancierListe M
  end;
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
  match goal with
  | |- Transformation _ ?M _ => instancierListe M
  end;
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
  match goal with
  | |- Transformation _ ?M _ => instancierListe M
  end;
  eapply (instanciationValeur 0); simpl; trivial; simpl;
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 n); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

(* Garde de Candidat1 *)

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

Ltac DeterminerC H3 H'' :=
  match H3 with
  | _ \/ ?H3' => destruct H'' as [H'' | H'']; 
                                        [tryif discriminate H'' 
                                        then simpl
                                        else injection H''; intros; subst; 
                                                tryif (left; omega) then simpl 
                                                                               else (do 2 eexists); intuition; reflexivity
                                        | ]; 
                                                DeterminerC H3' H''
  | _ = _      => tryif discriminate H''
                       then simpl
                       else injection H''; intros; subst; tryif (left; omega)
                                                                             then simpl 
                                                                             else (do 2 eexists); intuition; reflexivity
  end.

Ltac DeterminerT H2 H3 H' H'' :=
  match H2 with
  | _ \/ ?H2' => destruct H' as [H'|  H']; 
                        [ tryif discriminate H' then simpl else injection H'; intros; subst; simpl;
                        DeterminerC H3 H''| ]; DeterminerT H2' H3 H' H''
  | _ = _    => tryif discriminate H'
                     then simpl
                     else injection H'; intros; subst; DeterminerC H3 H''
  end.

Ltac DeterminerG H1 H2 H3 H H' H'' :=
   match H1 with
   | _ \/ ?H1' => destruct H; [tryif discriminate H
                                              then simpl
                                              else injection H; intros; subst;
                                                      DeterminerT H2 H3 H' H'' | ]; 
                                                      DeterminerG H1' H2 H3 H H' H''
   |  _ =_ => tryif discriminate H
                   then simpl
                   else injection H; intros; subst;
                            DeterminerT H2 H3 H' H''
   end.

Ltac resoudreDroite :=
   right; simpl; intros;
   match goal with
   | H : ?H1 /\ ?H2 /\ ?H3 |- _ => destruct H as [?H [?H' ?H'']]; DeterminerG H1 H2 H3 H H' H''
   end.


Ltac ConclureCandidat1 := idtac "";
                                              idtac "Résoudre la garde de Candidat1";
                                              idtac "Essai de la partie Gauche ";
                                              tryif left; simpl; intros; repeat (split; discriminate); reflexivity
                                              then idtac "Succès" else idtac "Échec"; right;
                                              idtac "Essai de la partie Droite -> Gauche ";
                                              tryif resoudreGauche then idtac "Succès !" else idtac "Échec";
                                              idtac "Essayer la partie Droite -> Droite";
                                              tryif resoudreDroite then idtac "Succès !" else idtac "Échec".

(* Garde de Candidat2 *)

Ltac DeterminerC2 H3 H'' :=
  match H3 with
  | _ \/ ?H3' => destruct H'' as [H'' | H'']; 
                                        [tryif discriminate H'' 
                                        then simpl
                                        else injection H''; intros; subst; 
                                                tryif (left; repeat (split; discriminate); reflexivity) 
                                                                               then simpl
                                                                               else right; simpl; intro
                                        | ]; DeterminerC2 H3' H''
  | _ = _      => tryif discriminate H''
                       then simpl
                       else injection H''; intros; subst; tryif (left; repeat (split; discriminate); reflexivity)
                                                                             then simpl 
                                                                             else right; simpl; intro
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
   simpl; intros;
   match goal with
   | H : ?H1 /\ ?H2 /\ ?H3 |- _ => destruct H as [?H [?H' ?H'']]; DeterminerG2 H1 H2 H3 H H' H''
   end.

Ltac ConclureCandidat2 := idtac "";
                                              idtac "Résoudre la garde de Candidat2";
                                              idtac "Essai de la partie Gauche ";
                                              tryif left; simpl; intros; repeat (split; discriminate); reflexivity
                                              then idtac "Succès" else idtac "Échec"; right;
                                              idtac "Essai de la partie Droite -> Gauche ";
                                              tryif resoudreGauche then idtac "Succès !" else idtac "Échec";
                                              right;
                                              idtac "Essayer la partie Droite -> Droite";
                                              tryif resoudreDroite2 then idtac "Succès !" else idtac "Échec".

(* Garde de Recouvrement *)

Ltac ConclureRecouvrement := 
  simpl; intros;
    match goal with
   | H : _ /\ _ |- _ => destruct H
   end;
   repeat (
   match goal with
   | H : _ \/ _ |- _ => destruct H; 
                               [ tryif (discriminate H) then simpl
                                                                     else  injection H; intros; subst; simpl in *;
                                                                              repeat (
                                                                              match goal with
                                                                              | H0 : _ \/ _ |- _ =>  destruct H0;
                                                                                                             [ tryif (discriminate H0) then simpl
                                                                                                               else  injection H0; intros; subst;
                                                                                                               eexists; intuition | ]
                                                                              | _ => try contradiction
                                                                              end)
                                 | ]
   | H : _ = _ |- _ => tryif (discriminate H) then simpl
                                                                   else  injection H; intros; subst; simpl in *;
                                                                            repeat (
                                                                            match goal with
                                                                            | H0 : _ \/ _ |- _ =>  destruct H0; [ tryif (discriminate H0) then simpl
                                                                                                                                    else  injection H0; intros; subst;
                                                                                                                                    eexists; intuition | ]
                                                                            | _                     => try contradiction
                                                                            end)
   end).

Definition règles push pop := [Candidat1 push; Candidat2 push; Recouvrement pop].

Definition grapheSimple := g 1 2 1 ⊗ g 2 3 2 ⊗ g 1 3 4.

(* Test simple avec structure de pile *)

Theorem recouvrementSimplePile :
  Transformation (règles push_pile pop_pile)
                 (grapheSimple  ⊗ c[(1,1,0)]) (grapheSimple ⊗ c[] ⊗ t 1 1 0 ⊗ t 1 2 1 ⊗ t 2 3 3).
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
  ConclureRecouvrement.
Qed.

(* Test simple avec structure de file *)

Theorem recouvrementSimpleFile :
  Transformation (règles push_file pop_file)
                 (grapheSimple  ⊗ c[(1,1,0)]) (grapheSimple ⊗ c[] ⊗ t 1 1 0 ⊗ t 1 2 1 ⊗ t 2 3 3).
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
  ConclureRecouvrement.
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

Theorem RecouvrementPile6Sommets : 
  Transformation (règles push_pile pop_pile)
                 (graphe6Sommets  ⊗ c[(1,1,0)]) 
                 (graphe6Sommets ⊗ c[] ⊗ t 1 1 0 ⊗ t 1 2 4 ⊗ t 1 4 1 ⊗ t 1 5 2 ⊗ t 5 6 3 ⊗ t 5 3 2).
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
  ConclureRecouvrement.
Qed.

End Pondéré.
