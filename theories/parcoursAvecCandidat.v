Require Import TactiquesParcours.
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
| C : @structure (nat*nat) -> At
| T : nat -> nat -> At.

Definition g := fun a b => atome (G a b).
Definition t := fun a b => atome (T a b).
Definition c := fun s => atome (C s).

(*
- G(a, b, n) : graphe décrit par la relation G contenant les arcs
- C = [(a1,b1,c1) ... (an, bn,cn)] : table des candidats avec une structure sous-jacente de file/pile
- T(a, b, n) : arbre couvrant décrit par la relation T (b parent de a) à distance n
 *)


(* G(a, b) & T(a', a) & ¬T(?, b) & ¬C(?, b) -> G(a, b) & T(a', a) & C(a, b) *)

Definition Candidat push :=
  ∀_v s, ∀_m X , ∀_v a , ∀_v b , ∀_v a',
          ((forall b', Absence (t a' a ⊗ X) (T b' b) /\ AbsenceListe s (b', b))
             ? (g a b ⊗ t a' a ⊗ c s ⊗ X) 
                        -o (g a b ⊗ t a' a ⊗ c (push (a, b) s) ⊗ X)).

(* C(a,b) & ¬T(?, b) -> T(a,b) *)

Definition Recouvrement1 pop :=
  ∀_v s , ∀_v s', ∀_m X , ∀_v a , ∀_v b,
            (((forall b', Absence X (T b' b)) /\ (pop s = Some((a,b),s')))
            ? (c s ⊗ X)
                -o (c s' ⊗ t a b ⊗ X)).

(* C(a,b) & T(b', b) -> T(b',b) *)

Definition Recouvrement2 (pop: @structure (nat*nat) -> option((nat*nat)*@structure(nat*nat))) :=
   ∀_v s , ∀_v s', ∀_m X , ∀_v a , ∀_v b , ∀_v b',
          ((pop s = Some((a,b),s'))
            ? (c s ⊗ t b' b ⊗ X)
              -o (c s' ⊗ t b' b ⊗ X)).

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1, T m2 n2 => (m1, n1) =? (m2, n2)
  | G m1 n1, G m2 n2 => (m1, n1) =? (m2, n2)
  | C s1, C s2 => s1 =? s2
  | _, _            => false
  end.

Definition grapheSimple := g 1 2 ⊗ g 2 3 ⊗ g 1 3.

(* Tactics *)
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

Ltac Recouvrement1 a b :=
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

Ltac Recouvrement2 a b b' :=
  match goal with
  | |- Transformation _?M _ => instancierListe M
  end;
  eapply (instanciationValeur 0); simpl; trivial; simpl;
  eapply (instanciationMolecule 0); simpl; trivial; simpl;
  eapply (instanciationValeur 0 a); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b); simpl; trivial; simpl;
  eapply (instanciationValeur 0 b'); simpl; trivial; simpl;
  eapply (reactionTransformation 0); simpl; trivial; simpl;
  try (apply identiteTransformation; [reflexivity | supprConjMultGauche]);
  auto; try supprNeutre.

Definition règles push pop := [exponentiel (Candidat push); exponentiel (Recouvrement1 pop)].

Theorem recouvrementSimple :
  Transformation (règles push_pile pop_pile)
                 (grapheSimple ⊗ c [(1,1)]) (grapheSimple ⊗ c [] ⊗ t 1 1 ⊗ t 1 2 ⊗ t 2 3).
Proof.
  (* Generate t 1 1 *)
  dupliquerExponentielle 1.
  Recouvrement1 1 1.

  (* Generate C 1 2 *)
  dupliquerExponentielle 0.
  Candidat 1 2 1.

  (* Generate T 1 2 *)
  dupliquerExponentielle 1.
  Recouvrement1 1 2.

  (* Generate C 2 3 *)
  dupliquerExponentielle 0.
  Candidat 2 3 1.

  (* Generate T 2 3 *)
  dupliquerExponentielle 1.
  Recouvrement1 2 3.
  Conclure.
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

Definition Candidat1 push :=
  ∀_v s, ∀_m X , ∀_v a , ∀_v b , ∀_v n , ∀_v a' , ∀_v da,
          ((forall b1 b2, Absence (t a' a da ⊗ X) (T b1 b b2) /\ AbsenceListe s (b1, b, b2))
             ? (g a b n ⊗ t a' a da ⊗ c s ⊗ X) -o (g a b n ⊗ t a' a da ⊗ c (push (a, b, da + n) s) ⊗ X)).

(* G(a, b, n) & T(a', a, da) & ¬T(?, b, ?) & C(?, b, db) & (da + n < db) 
                                  -> G(a, b, n) & T(a', a, da) & C(a, b, da + n) *)

Definition Candidat2 push :=
  ∀_v s, ∀_m X , ∀_v a , ∀_v b , ∀_v n,
  ∀_v a', ∀_v da , ∀_v b' , ∀_v db,
          (((forall b1 b2, Absence (t a' a da ⊗ X) (T b1 b b2)) /\ In (b', b, db) s /\ (da + n < db) )
             ? (g a b n ⊗ t a' a da ⊗ c s ⊗ X) -o (g a b n ⊗ t a' a da ⊗ c (replace (b', b, db) (a, b, da + n) s push) ⊗ X)).

(* G(a, b, n) & T(a', a, da) & T(?, b, db) & ¬ C(?, b, ?) & (da + n < db) 
                                  -> G(a, b, n) & T(a', a, da) & C(a, b, da + n) *)

Definition Candidat3 push :=
  ∀_v s, ∀_m X , ∀_v a , ∀_v b , ∀_v n,
  ∀_v a', ∀_v da , ∀_v b' , ∀_v db,
          (((forall b1 b2, AbsenceListe s (b1, b, b2)) /\ (da + n < db) )
             ? (g a b n ⊗ t a' a da ⊗ t b' b db ⊗ c s ⊗ X) -o (g a b n ⊗ t a' a da ⊗ c (push (a, b, (da + n)) s) ⊗ X)).

(* G(a, b, n) & T(a', a, da) & T(?, b, db) & (da + n < db) & C (?, b, db') & (da + n < db') 
                                  -> G(a, b, n) & T(a', a, da) & C(a, b, da + n) *)

Definition Candidat4 push :=
  ∀_v s, ∀_m X , ∀_v a , ∀_v b , ∀_v n,
  ∀_v a', ∀_v da , ∀_v b1 , ∀_v db1 , ∀_v b2 , ∀_v db2,
          (((In (b2, b, db2) s) /\ (da + n < db1) /\ (da + n < db2) )
             ? (g a b n ⊗ t a' a da ⊗ t b1 b db1 ⊗ c s ⊗ X)
                                  -o (g a b n ⊗ t a' a da ⊗ c (replace (b2, b, db2) (a, b, da + n) s push) ⊗ X)).

(* C(a,b,db) & ¬T(?,b,?) -> T(a,b,db) *)

Definition Recouvrement1 pop :=
  ∀_v s , ∀_v s', ∀_m X , ∀_v a , ∀_v b , ∀_v db,
        (((forall b1 b2, Absence X (T b1 b b2)) /\ (pop s = Some ((a,b,db),s')) )
        ? (c s ⊗ X) -o (c s' ⊗ t a b db ⊗ X)).

(* C(a,b,db) & T(?, b, db') & (db < db') -> T(a,b,db) *)

Definition Recouvrement2 pop :=
  ∀_v s, ∀_v s', ∀_m X , ∀_v a , ∀_v b , ∀_v db , ∀_v b' , ∀_v db',
          (((db < db') /\ (pop s = Some ((a,b,db),s')) ) 
          ? (c s ⊗ t b' b db' ⊗ X) -o (c s' ⊗ t a b db ⊗ X)).

(* C(a,b,db) & T(b', b, db') & ¬(db < db') -> T(b',b,db') *)

Definition Recouvrement3 (pop: @structure (nat*nat*nat) -> option ((nat*nat*nat)*@structure(nat*nat*nat))) :=
  ∀_v s , ∀_v s', ∀_m X , ∀_v a , ∀_v b , ∀_v db , ∀_v b' , ∀_v db',
          ( ((db' <= db) /\ (pop s = Some ((a,b,db),s')) )
          ? (c s ⊗ t b' b db' ⊗ X) -o (c s' ⊗ t b' b db' ⊗ X)).

Instance eqb_at : Eqb At :=
  fun x y =>
  match x, y with
  | T m1 n1 p1, T m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | G m1 n1 p1, G m2 n2 p2 => (m1, n1, p1) =? (m2, n2, p2)
  | C s1, C s2 => s1 =? s2
  | _, _            => false
  end.

Definition grapheSimple := g 1 2 1 ⊗ g 2 3 2 ⊗ g 1 3 4.

(* Tactics *)

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

Definition règles push pop := [exponentiel (Candidat1 push); exponentiel (Candidat2 push);
                                                    exponentiel (Recouvrement1 pop)].

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
  Conclure.
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
  Conclure.
Qed.
(* Un exemple à 6 sommets :                                 Dois mener à l'arbre couvrant T suivant :
          (1 est racine)

    ---------------------------------------                                                 1 ----------- 2
   |                                              |                                                / \
   |                                             ⋁                                       /   \
   |            1 ---------  (4)  -------> 2 <----------                             4     5
   |            / \                                                \                                  /  \
  (4)        /    \                                               |                                /     \
   |        (1)     ---- (2) ----                              |                              6      3
   |         /                       |                            (3)
   |        /                       ⋁                        |
   ----- 4 ------ (2) ------> 5 ---------(0)-------> 3
           |                         |
           |                       (1)
           |                         |
           |                        ⋁
           --------(3)-------> 6                                                                                                          *)






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
  Conclure.
Qed.

End Pondéré.

