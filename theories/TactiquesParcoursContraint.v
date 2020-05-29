Require Export Egalite ReactionsTransformations ReactionsTransformationsMeta.
Require Import List Nat Omega.
Import ListNotations.

(** Added atomic equality *)

Local Open Scope eqb_scope.

Instance: EqbSpec (nat*nat).
Proof.
  apply eqbspec_couples.
Qed.

Instance: EqbSpec (nat*nat*nat).
Proof.
  apply eqbspec_couples.
Qed.

Instance eqb_atomes{A:Type}`{Eqb A} : Eqb Molecule :=
  fun (m1 m2: @Molecule A) =>
  match m1, m2 with
  | un, un => true
  | atome a1, atome a2 => a1 =? a2
  | _, _ => false
  end.

(** Tactiques *)

Ltac premierGauche n := eapply (premierGauche n); try reflexivity; simpl.

(* Plusieurs premierGauche successifs *)
Ltac premierGaucheListe l :=  
  match l with
  | ?n::?l' => premierGauche n; premierGaucheListe l'
  | [] => simpl
  end.

(* Il faudrait peut être le placer ailleurs? Toujours est il qu'il est utilisé dans
 la tactique suivante (supprConjMultGauche)*)
Lemma associativiteConjonctionMultiplicativeGauche :
  forall A : Type, forall M1 M2 M3 : (@Molecule A),
      forall G N,
        EquivalenceMoleculaire (( M1 ⊗ M2 ⊗ M3 ) :: G) N
        -> EquivalenceMoleculaire (( M1 ⊗ (M2 ⊗ M3)) :: G) N.
Proof.
  intros A M1 M2 M3 G N H.
  apply conjonctionMultiplicativeGauche.
  eapply (premierGauche 1). 
  unfold valeur; simpl.
  destruct G; simpl; reflexivity.
  simpl.
  apply conjonctionMultiplicativeGauche.
  eapply (premierGauche 2).
  unfold valeur; destruct G; simpl; reflexivity.
  simpl.
  destruct G; simpl;
  apply equivalenceDefinitionEquivalenceMoleculaireP;
  do 2 eapply (inversionConjonctionMultiplicativeGauche _ _ _ []); simpl;
  apply equivalenceDefinitionEquivalenceMoleculaire; assumption.
Qed.

(* Tactique qui supprime toutes les occurence de ⊗ à gauche de l'EquivalenceMoleculaire
    M1 ⊗ ... ⊗ Mn ≡ ...             =>            M1, ... , Mn ≡ ...
*)

Ltac supprConjMultGauche := 
(* La Molecule est d'abord mise sous une forme normale (ie (((A1⊗A2)⊗A3) ... ) en utilisant
   l'associativité *)
repeat (apply associativiteConjonctionMultiplicativeGauche);
repeat (eapply (conjonctionMultiplicativeGauche)).

(** Force the transform of any left multiplicative conjunction into a list
    Complex, thus to use when no other choice. Otherwise, try supprConjMultGauche *)

Ltac FormeNormaleGaucheRec L n next_tactic :=
  match L with
  | [] => idtac "Molecule under normal form"
  | ?M :: ?L' => match M with
                         | ?M1 ⊗ ?M2 => premierGauche n; next_tactic
                         | atome ?a    => FormeNormaleGaucheRec L' (S n) next_tactic
                         | un                  => FormeNormaleGaucheRec L' (S n) next_tactic
                         end
  end.

Ltac FormeNormaleGauche :=
  supprConjMultGauche;
  match goal with
  | |- EquivalenceMoleculaire ?L _ => FormeNormaleGaucheRec L 0 FormeNormaleGauche
  end.

Ltac conjonctionMultiplicativeDroite n := 
match n with
| 0 => repeat (eapply identiteAtome); simpl
| 1 => repeat (eapply identiteAtome); simpl
| S ?n' => try (eapply (conjonctionMultiplicativeDroite n')); conjonctionMultiplicativeDroite n'
end.

Lemma associativiteConjonctionMultiplicativeDroite :
  forall A : Type, forall N, forall M1 M2 M3 : (@Molecule A),
        EquivalenceMoleculaire N (M1 ⊗ M2 ⊗ M3)
        -> EquivalenceMoleculaire N (M1 ⊗ (M2 ⊗ M3)).
Proof.
  intros. apply (coupureMolecule (length N) (M1 ⊗ M2 ⊗ M3)).
  rewrite prefixeEnFin; trivial.
  rewrite suffixeEnFin.
  apply symmetrieMoleculaire.
  apply associativiteConjonctionMultiplicativeGauche.
  apply reflexiviteMoleculaire.
Qed.

Lemma associativiteConjonctionMultiplicativeDroite2 :
  forall A : Type, forall N, forall M1 M2 M3 M4 : (@Molecule A),
        EquivalenceMoleculaire N (M1 ⊗ M2 ⊗ M3 ⊗ M4)
        -> EquivalenceMoleculaire N (M1 ⊗ (M2 ⊗ M3) ⊗ M4).
Proof.
  intros. apply (coupureMolecule (length N) (M1 ⊗ M2 ⊗ M3 ⊗ M4)).
  rewrite prefixeEnFin; trivial.
  rewrite suffixeEnFin.
  apply symmetrieMoleculaire.
  supprConjMultGauche.
  premierGauche 1.
  apply conjonctionMultiplicativeGauche.
  premierGaucheListe [3; 2; 2;3].
  conjonctionMultiplicativeDroite 4; apply reflexiviteMoleculaire.
Qed.

Ltac formeNormaleDroite := repeat (apply associativiteConjonctionMultiplicativeDroite).

Ltac supprNeutre :=
  apply (neutreTransformation 0); simpl; trivial.

Ltac resoudreMoleculeInconnue :=
  repeat (eapply (conjonctionMultiplicativeDroite 1); try eapply identiteAtome).

Ltac resoudreAbsences := intros; repeat (split; try discriminate).

Ltac reordonnerAutomatiquementRec M :=
  match goal with
  | |- EquivalenceMoleculaire ?l _ =>
                     match M with 
                     | ?M'⊗?At =>
                         match eval compute in (indexOf At l) with
                         | Some ?n => premierGauche n; reordonnerAutomatiquementRec M'
                         end
                     | ?At =>
                         match eval compute in (indexOf At l) with
                         | Some ?n => premierGauche n
                         | None       => simpl
                         end
                     end
  end.

Ltac reordonnerAutomatiquement :=
  match goal with
  | |- EquivalenceMoleculaire ?l ?M => 
                reordonnerAutomatiquementRec M; 
                conjonctionMultiplicativeDroite eval compute in (length l)
  end;
  try apply (conjonctionMultiplicativeDroite 0); simpl;
  try apply unDroite; 
  try eapply identiteAtome.

Ltac reordonnerAutomatiquementExistentielle :=
  match goal with
  | |- EquivalenceMoleculaire _ (?M⊗_) =>
                match eval compute in (tailleMolecule M) with
                | ?m => reordonnerAutomatiquementRec M; 
                              apply (conjonctionMultiplicativeDroite m);
                              try (conjonctionMultiplicativeDroite m; reflexivity)
                end
  end.

Ltac dupliquerExponentielle n :=
  eapply (conjonctionAdditiviteDroiteTransformation n); [ reflexivity | simpl];
  eapply (conjonctionMultiplicativeTransformation n); [ reflexivity | simpl];
   eapply (premiereRegle n); [ reflexivity | simpl].

Ltac PlusDeGC := left; red; intros; simpl; repeat(split; try discriminate); reflexivity.

Ltac PlusDeCListe :=
  left; red ; simpl; intuition;
  try(match goal with
        | H : _ |- _ => try discriminate H; injection H; intro; subst; reflexivity
        end
        ); reflexivity.

Ltac ChoisirNeutrePartoutRec n :=
   eapply (conjonctionAdditiviteGaucheTransformation 0); [reflexivity | simpl];
   eapply (instanciationMolecule 0 ); [reflexivity | simpl];
   eapply (reactionTransformation 0); simpl;
   [reflexivity
   | apply identiteTransformation; 
              [reflexivity | supprConjMultGauche; resoudreMoleculeInconnue ]
   | try PlusDeGC; try PlusDeCListe; try right
   | supprNeutre;
     match goal with 
     | |- Transformation ?l _ _ => match l with
                                   | [] => apply identiteTransformation; [reflexivity |
                                           supprConjMultGauche; repeat apply inversionC; 
                                           apply symmetrieMoleculaire; cbv delta; 
                                           FormeNormaleGauche; 
                                           idtac "There is/are" n "guard constraint(s) to solve.";
                                           reordonnerAutomatiquement]
                                   | ?x :: ?l' => ChoisirNeutrePartoutRec (S n)
                                   end
     end
    ].

Ltac ChoisirNeutrePartout := ChoisirNeutrePartoutRec 0.

(* Essayer avec auto de tout résoudre seul *)
Hint Extern 4 (forall _, Absence _ _) => try resoudreAbsences.
Hint Extern 4 (_ /\ _) => try resoudreAbsences.
Hint Extern 4 (_ /\ _ /\ _) => try resoudreAbsences; simpl; intuition; omega.
Hint Extern 4 (_ = _) => try resoudreAbsences.
Hint Extern 4 (EquivalenceMoleculaire _ _) => try resoudreMoleculeInconnue.
Hint Extern 4 (EquivalenceMoleculaire _ _) => try reordonnerAutomatiquementExistentielle.
Hint Extern 4 (Transformation (neutreRegle :: _) _ _) => try supprNeutre.
Hint Extern 4 (Transformation [] _ _) => try (eapply identiteTransformation; trivial;
                                                                                     supprConjMultGauche; cbv delta;
                                                                                     reordonnerAutomatiquement).

Ltac simplBlocage :=
  tryif (apply blocageConjonctionAdditive; intros)
  then simplBlocage
  else tryif (apply blocageConjonctionMultiplicative; intros)
          then simplBlocage
          else tryif (apply blocageQuantificationMolecule; intros)
                  then simplBlocage
                  else tryif (apply blocageQuantificationValeur; intros)
                          then simplBlocage
                          else tryif (apply blocageReaction; intros)
                                  then simplBlocage
                                  else tryif (apply blocageReactionAvecContinuation; intros)
                                          then simplBlocage
                                          else unfold not; intros.