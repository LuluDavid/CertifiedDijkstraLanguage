Require Export molecules_meta.

Import ListNotations.


(*
 * - règle r ::= reaction 
 *             | ∀x. r | ∀X.r (quantification sur des valeurs | sur des molécules)
 *             | r ⊠ r | r ∧ r (conjonctions multiplicative et additive)
 * - réaction ::= g ? M1 -o M2, regle (implication linéaire avec une 
 *                                     conjonction multiplicative à gauche)
 * - garde g : Prop
 * (règle := schéma de réaction)
 *)
CoInductive Regle{A : Type}
  : Type
  :=
  | neutreRegle : Regle  
  | reaction :
      forall M1 M2 : (@Molecule A), forall r : Regle, forall g : Prop, Regle
  | quantificationValeur :
      forall V : Type,
      (V -> Regle)
      -> Regle
  | quantificationMolecule :
      ((@Molecule A) -> Regle)
      -> Regle
  | conjonctionMultiplicativeRegles : Regle -> Regle -> Regle
  | conjonctionAdditiveRegles : Regle -> Regle -> Regle
.


(* TODO vérifier les niveaux ! *)
Notation "g '?' x -o y" := (reaction x y neutreRegle g) (at level 10).
Notation "g '?' x --o y ',' r" := (reaction x y r g) (at level 10).
Notation "'∀2' r" := (quantificationMolecule r) (at level 5).
Notation "'∀1' r" := (quantificationValeur _ r) (at level 5).
Notation "'∀_m' X , r" := (∀2 (fun X => r)) (at level 5).
Notation "'∀_v' x , r" := (∀1 (fun x => r)) (at level 5).
Notation "r1 ⊠ r2" := (conjonctionMultiplicativeRegles r1 r2) (at level 18, right associativity).
Notation "r1 ∧ r2" := (conjonctionAdditiveRegles r1 r2) (at level 19, right associativity).

Definition exponentiel{A : Type}(r : @Regle A) : @Regle A.
  cofix E.
  exact (neutreRegle ∧ r ∧ (E ⊠ E)).
Defined.

Print exponentiel. (* ⊠ prioritaire / ∧ *)

Notation "'E!' r" := (exponentiel r) (at level 6).

Definition depliageRegle{A : Type}(r : @Regle A) : @Regle A.
  destruct r as [ | M1 M2 r g | V r | r | r1 r2 |r1 r2].
  {
    exact neutreRegle.
  }
  {
    exact (g ? M1 --o M2, r).
  }
  {
    exact (∀1 r).
  }
  {
    exact (∀2 r).
  }
  {
    exact (r1 ⊠ r2).
  }
  {
    exact (r1 ∧ r2).
  }
Defined.

(* Projections utiles pour simplifier la décomposition d'une égalité (dans le 
 * cas quantificationValeur) *)

Print unit.

Definition projectionTypeQuantificationValeur{A : Type}(R : @Regle A) : Type.
  destruct R as [ | | V _ | _ | _ | _ ].
  {
    exact unit.
  }
  {
    exact unit.
  }
  {
    exact V.
  }
  {
    exact unit.
  }
  {
    exact unit.
  }
  {
    exact unit.
  }
Defined.

Definition projectionFonctionQuantificationValeur{A : Type}
           (R : @Regle A)
           (v : projectionTypeQuantificationValeur R) : @Regle A.
  destruct R as [ | M1 M2 r g | V r | r | r1 r2 | r1 r2].
  {
    exact neutreRegle.
  }
  {
    exact (g ? M1 --o M2, r).
  }    
  {
    simpl in v.
    exact (r v).
  }
  {
    exact (∀2 r).
  }
  {
    exact (r1 ⊠ r2).
  }
  {
    exact (r1 ∧ r2).
  }
Defined.

(*
- Théorie de la démonstration - 
  Séquent : liste de règles, molécule ⊢ molécule
- La molécule à droite indique le résultat du calcul. 
  Il n'y a plus besoin de prédicat exprimant la terminaison.

        R1, R2, M1 ⊢ M2
[1-G] ---------------------
       R1, 1, R2, M1 ⊢ M2

            M1 ⊢ M2
[ID-G] ----------------
       [], M1 ⊢ M2

          ⊢ g   R1, MA ⊢ M1   r, R2, M2 ⊢ MB
[-o-G] ----------------------------------------
           R1, (g ? M1 --o M2, r), R2, MA ⊢ MB

         R1, r[x := v], R2, MA ⊢ MB
[∀1-G] --------------------------------
           R1, ∀x. r, R2, MA ⊢ MB

         R1, r[X := M], R2, MA ⊢ MB
[∀2-G] -------------------------------
          R1, ∀X. r, R2, MA ⊢ MB

            R1, MA ⊢ M   R2, M ⊢ MB
[Coupure-G] -----------------------
               R1, R2, MA ⊢ MB

         R1, r1, r2, R2, M1 ⊢ M2
[⊠-G]  ----------------------------
         R1, r1 ⊠ r2, R2, M1 ⊢ M2

         R1, r1 | r2, R2, M1 ⊢ M2
[∧-G]  ---------------------------
         R1, r1 ∧ r2, R2, M1 ⊢ M2

+ permutations pour les règles (déplacements en tête ou de la tête en
  chaînage arrière ou avant respectivement)

*)

Inductive Transformation{A : Type}
          (R : list (@Regle A)) (* règles *)
          (M1 : @Molecule A) (* molécule 1 *)
          (M2 : @Molecule A) (* molécule 2 *) 
  : Prop
  := 
  | neutreTransformation :
      forall n,
        map depliageRegle (valeur n R) = [neutreRegle]
        -> Transformation ((prefixe n R) ++ (suffixe (S n) R)) M1 M2
        -> Transformation R M1 M2
  | identiteTransformation :
      R = []
      -> EquivalenceMoleculaire [M1] M2
      -> Transformation R M1 M2
  | reactionTransformation :
      forall n (g : Prop) N1 N2 r,
        map depliageRegle (valeur n R) = [g ? N1 --o N2, r]
        -> Transformation (prefixe n R) M1 N1
        -> g
        -> Transformation (r :: (suffixe (S n) R)) N2 M2
        -> Transformation R M1 M2
  | instanciationValeur :
      forall n T v (r : T -> (@Regle A)),
        map depliageRegle (valeur n R) = [∀1 r]
        -> Transformation (prefixe n R ++ [r v] ++ suffixe (S n) R) M1 M2
        -> Transformation R M1 M2
  | instanciationMolecule : 
      forall n X r,
        map depliageRegle (valeur n R) = [∀2 r]
        -> Transformation (prefixe n R ++ [r X] ++ suffixe (S n) R) M1 M2 
        -> Transformation R M1 M2
  | conjonctionMultiplicativeTransformation :
      forall n, forall r1 r2,
          map depliageRegle (valeur n R) = [r1 ⊠ r2]
          -> Transformation (prefixe n R ++ [r1] ++ [r2] ++ suffixe (S n) R) M1 M2
          -> Transformation R M1 M2
  | conjonctionAdditiviteGaucheTransformation :
      forall n, forall r1 r2,
          map depliageRegle (valeur n R) = [r1 ∧ r2]
          -> Transformation (prefixe n R ++ [r1] ++ suffixe (S n) R) M1 M2
          -> Transformation R M1 M2
  | conjonctionAdditiviteDroiteTransformation :
      forall n, forall r1 r2,
          map depliageRegle (valeur n R) = [r1 ∧ r2]
          -> Transformation (prefixe n R ++ [r2] ++ suffixe (S n) R) M1 M2
          -> Transformation R M1 M2
  | premiereRegle :
      forall n r,
        (map depliageRegle (valeur n R) = [r])
        -> Transformation (r :: ((prefixe n R) ++ (suffixe (S n) R))) M1 M2
        -> Transformation R M1 M2
  | coupureRegles :
      forall n N,
        Transformation (prefixe n R) M1 N                       
        -> Transformation (suffixe n R) N M2
        -> Transformation R M1 M2.

Arguments Transformation {_}.
Arguments neutreTransformation {_ _ _ _ }.
Arguments identiteTransformation {_ _ _ _ }.
Arguments reactionTransformation {_ _ _ _ }.
Arguments  instanciationValeur {_ _ _ _ } n {_}.
Arguments  instanciationMolecule {_ _ _ _ }.
Arguments  conjonctionMultiplicativeTransformation { _ _ _ _ }.
Arguments  conjonctionAdditiviteGaucheTransformation { _ _ _ _ }.
Arguments  conjonctionAdditiviteDroiteTransformation { _ _ _ _ }.
Arguments  premiereRegle {_ _ _ _ }.
Arguments  coupureRegles {_ _ _ _ }.


(* Blocage *)

Definition Blocage{A : Type}(R : list (@Regle A))(M1 : @Molecule A) : Prop :=
  forall M2, ~(Transformation R M1 M2).

Definition neutreRegleBlocage{A : Type}(r : @Regle A) : @Regle A.
exact (∀2 (fun Y => (Blocage [r] Y) ? Y -o Y)).
Defined.

Definition exponentielDeterministe{A : Type}(r : @Regle A) : @Regle A.
  cofix E.
  exact ((neutreRegleBlocage r) ∧ (r ⊠ E)).
Defined.











