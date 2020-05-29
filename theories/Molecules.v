Require Export PrefixesSuffixesMeta.

Import ListNotations.

Inductive Habitation(A : Type)
  : Prop
  :=
  | habitant : forall temoin : A, Habitation A. 

Arguments habitant {_}.

Definition conversion{A B}(x : A)(eq : A = B) : B.
  rewrite <- eq.
  exact x.
Defined.

Definition egaliteAntecedents{A B}(f : A -> B){x x' : A}{y y': B} :
  (x = x') -> (f x = y) -> (f x' = y')
  -> y = y'.  
  intro eqA.
  rewrite eqA.
  intros.
  transitivity (f x').
  symmetry; assumption.
  assumption.
Defined.

(*******************************************************************)

(* 
* Version 6a - plongement superficiel
*)


(* 
Molécule et équivalence moléculaire : fragment de la logique linéaire
- neutre multiicatif : 1
- conjonction multiplicative : ⊗

Molécule := une conjonction multiplicative d'atomes 
- molécule ::= 1 | A | M ⊗ M
- atome A ::= P t* | 
- P : Prédicat 
- t : Val

Remarque : le langage est paramétré par un ensemble d'atomes, à définir à chaque utilisation.

Equivalence moléculaire - Théorie de la démonstration (calcul des séquents)
- séquent intuitionniste : (list M) ⊢ M 

[ID] ----------- ou -----------
       [M] ⊢ M         [A] ⊢ A 
           
           Γ ⊢ N   Δ, N ⊢ M 
[coupure] ------------------
             Γ, Δ ⊢ M

        Γ ⊢ M
[1-G] -----------    [1-D] ------
       1, Γ ⊢ M             ⊢ 1

          M1, M2, Γ ⊢ M            Γ ⊢ M1    Δ ⊢ M2
[⊗-G]  ------------------   [⊗-D] ------------------
         M1 ⊗ M2, Γ ⊢ M             Γ, Δ ⊢ M1 ⊗ M2

+ permutation sous la forme de règles de focalisation

 *)

Inductive Molecule{A : Type}
  : Type
  :=
  | un :
      Molecule (* neutre multiplicatif *)
  | atome :
      A -> Molecule
  | conjonctionMultiplicative :
      Molecule -> Molecule -> Molecule.

Notation "M ⊗ N" := (conjonctionMultiplicative M N) (at level 20, left associativity).


Fixpoint tailleMolecule{A:Type} (M:@Molecule A) :=
  match M with
  | M1 ⊗ M2 => tailleMolecule M1 + tailleMolecule M2
  | _             => 1
  end.

Inductive EquivalenceMoleculaire{A : Type}
  : list (@Molecule A)
    -> (@Molecule A)
    -> Prop
  :=
  (* Groupe identité *)
  | identiteAtome :
      forall a, EquivalenceMoleculaire [atome a] (atome a) 
  (* Elements neutres *)
  | unDroite : EquivalenceMoleculaire [] un
  | unGauche : forall LM M,
      EquivalenceMoleculaire LM M ->
      EquivalenceMoleculaire (un :: LM) M
  (* Groupe Multiplicatif *)
  | conjonctionMultiplicativeDroite : forall g, forall LM M1 M2, 
        EquivalenceMoleculaire (prefixe g LM) M1 ->
        EquivalenceMoleculaire (suffixe g LM) M2 ->
        EquivalenceMoleculaire LM (M1 ⊗ M2)
  | conjonctionMultiplicativeGauche : forall LM, forall M1 M2 M,
        EquivalenceMoleculaire (M1 :: M2 :: LM) M -> 
        EquivalenceMoleculaire ((M1 ⊗ M2) :: LM) M
  (* Partition de la liste gauche *)
  | premierGauche : forall n LM LMn M,
      valeur n LM = [LMn] ->
      EquivalenceMoleculaire (LMn :: ((prefixe n LM) ++ (suffixe (S n) LM))) M ->
      EquivalenceMoleculaire LM M.

(* 
- P pour définition paramétrée 
- elle facilite l'inversion.
*)
Inductive EquivalenceMoleculaireP{A : Type}
          (LM : list (@Molecule A))
          (M : @Molecule A)
  : Prop
  :=
  (* Groupe identité *)
  | identiteAtomeP :
      forall a, LM = [atome a] -> M = atome a
                -> EquivalenceMoleculaireP LM M
  (* Elements neutres *)
  | unDroiteP : LM = [] -> M = un -> EquivalenceMoleculaireP LM M
  | unGaucheP : forall LM',
      (LM = un :: LM')
      -> EquivalenceMoleculaireP LM' M
      -> EquivalenceMoleculaireP LM M
  (* Groupe Multiplicatif *)
  | conjonctionMultiplicativeDroiteP : forall g, forall M1 M2, 
        M =(M1 ⊗ M2)
        -> EquivalenceMoleculaireP (prefixe g LM) M1
        -> EquivalenceMoleculaireP (suffixe g LM) M2
        -> EquivalenceMoleculaireP LM M
  | conjonctionMultiplicativeGaucheP : forall LM', forall M1 M2,
        LM = (M1 ⊗ M2) :: LM'
        -> EquivalenceMoleculaireP (M1 :: M2 :: LM') M
        -> EquivalenceMoleculaireP LM M
  (* Partition de la liste gauche *)
  | premierGaucheP : forall n LMn,
      valeur n LM = [LMn] ->
      EquivalenceMoleculaireP (LMn :: ((prefixe n LM) ++ (suffixe (S n) LM))) M ->
      EquivalenceMoleculaireP LM M.

Definition reductionListeMoleculesEnConjonctionMultiplicative{A : Type} :
  list (@Molecule A) -> @Molecule A.
  fix REC 1.
  intro l.
  destruct l as [ | M k].
  {
    exact un.
  }
  {
    exact (M ⊗ (REC k)).
  }
Defined.

Inductive OccurrenceP{A : Type}(a : A)(M : @Molecule A)
  : Type
  :=
  | occurrenceAtomeP : (M = atome a) -> OccurrenceP a M 
  | occurrenceConjonctionGaucheP : forall M1 M2,
      (M = M1 ⊗ M2) -> OccurrenceP a M1 -> OccurrenceP a M
  | occurrenceConjonctionDroiteP : forall M1 M2,
      (M = M1 ⊗ M2) -> OccurrenceP a M2 -> OccurrenceP a M.

Inductive Occurrence{A : Type}(a : A) :
  (@Molecule A) -> Prop
  :=
  | occurrenceAtome : Occurrence a (atome a) 
  | occurrenceConjonctionGauche : forall M1 M2,
      Occurrence a M1 -> Occurrence a (M1 ⊗ M2)
  | occurrenceConjonctionDroite : forall M1 M2,
      Occurrence a M2 -> Occurrence a (M1 ⊗ M2).

Definition effacementAtome{A : Type}(a : A)
  : forall M, OccurrenceP a M -> @Molecule A.
  fix REC 2.
  intros M Occ.
  destruct Occ as [eqMa | M1 M2 eqM Occ1 | M1 M2 eqM Occ2].
  {
    exact un.
  }
  {
    exact ((REC M1 Occ1) ⊗ M2).
  }
  {
    exact (M1 ⊗ (REC M2 Occ2)).
  }
Defined.

Definition occurrenceAtomePGauche{A : Type}(a : A)(N : @Molecule A) :
  OccurrenceP a (atome a ⊗ N).
    eapply occurrenceConjonctionGaucheP.
    reflexivity.
    apply occurrenceAtomeP.
    reflexivity.
Defined.

(*
- Prédicat d'absence
 *)
Definition Absence
           {A: Type}
  : (@Molecule A) -> A -> Prop.
  fix HR 1.
  intros M a.
  destruct M as [ | b | M1 M2].
  {
    exact True.
  }
  {
    exact (a <> b).
  }
  {
    exact ((HR M1 a) /\ (HR M2 a)).
  }
Defined.

Definition Presence
           {A: Type}
  : (@Molecule A) -> A -> Prop.
  fix HR 1.
  intros M a.
  destruct M as [ | b | M1 M2].
  {
    exact False.
  }
  {
    exact (a = b).
  }
  {
    exact ((HR M1 a) \/ (HR M2 a)).
  }
Defined.

