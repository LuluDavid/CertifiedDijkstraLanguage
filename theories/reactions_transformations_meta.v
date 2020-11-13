Require Export reactions_transformations.

Import ListNotations.

Proposition compatibiliteEquivalenceMoleculaire_transformation :
  forall (A : Type)(R : list (@Regle A))(M1 M2 N: @Molecule A),
    Transformation R M1 N
    -> EquivalenceMoleculaire [M1] M2
    -> Transformation R M2 N.
Proof.
  fix HR 6.
  intros A R M1 M2 N HT EqM.
  case HT as [ n egN
             | eqR egN
             | n g N1 N2 r egN abs1 cg HT
             | n T v r1 egN
             | n X r2 egN
             | n r1 r2 egN
             | n r1 r2 egN
             | n r1 r2 egN
             | n r egN
             | n N' HTG HTD].
  {
    apply (neutreTransformation n).
    assumption.
    apply HR with M1.
    assumption.
    assumption.
  }
  {
    apply identiteTransformation.
    assumption.
    apply transitiviteMoleculaire with M1.
    apply symmetrieMoleculaire.
    assumption.
    assumption.
  }
  {
    apply reactionTransformation with n g N1 N2 r; try assumption.
    apply HR with M1; assumption.
  }
  {
    apply (instanciationValeur n v r1); try assumption.
    apply HR with M1; assumption.
  }
  {  
    apply (instanciationMolecule n X r2); try assumption.
    apply HR with M1; assumption.
  }
  {
    apply (conjonctionMultiplicativeTransformation n r1 r2); try assumption.
    apply HR with M1; assumption.
  }
  {
    apply (conjonctionAdditiviteGaucheTransformation n r1 r2); try assumption.
    apply HR with M1; assumption.
  }
  {
    apply (conjonctionAdditiviteDroiteTransformation n r1 r2); try assumption.
    apply HR with M1; assumption.
  }
  {
    apply (premiereRegle n r); try assumption.
    apply HR with M1; assumption.
  }
  {
    apply (coupureRegles n N'); try assumption.
    apply HR with M1; assumption.
  }
Qed.

Lemma deplierRegle :
  forall A, forall r : @Regle A,
      r = depliageRegle r.
Proof.
  intros A r.
  destruct r; reflexivity.
Qed.

(* Projection de l'égalité - Forme faible. *)
Proposition projectionEgaliteFonctionQuantificationValeur :
  forall A : Type,
  forall r1 r2 : @Regle A,
  forall (v : projectionTypeQuantificationValeur r1),
    r1 = r2 -> exists u, projectionFonctionQuantificationValeur r1 v
                       = projectionFonctionQuantificationValeur r2 u.
Proof.
  intros A r1 r2 v eqR.
  destruct eqR.
  destruct r1 as [ | M1 M2 r g | V r | r | r1 r2 | r1 r2];
    (simpl; exists v; reflexivity).
Qed.

(* Projection de l'égalité - Forme forte. *)
Proposition projectionEgaliteFonctionQuantificationValeur_constructif :
  forall A : Type,
  forall r1 r2 : @Regle A,
  forall (v : projectionTypeQuantificationValeur r1),
    r1 = r2
    -> exists eqT
              : (projectionTypeQuantificationValeur r1
                 = projectionTypeQuantificationValeur r2),
      projectionFonctionQuantificationValeur r1 v
      = projectionFonctionQuantificationValeur r2 (conversion v eqT).
Proof.
  intros A r1 r2 v eqR.
  destruct eqR.
  exists eq_refl.
  destruct r1 as [ | M1 M2 r g | V r | r | r1 r2 |r1 r2];
    (simpl; reflexivity).
Qed.

(* Admissibilité de différentes règles
 * - permutation des règles linéaires : dernier (comme premier) à gauche
 * - TODO coupure
 *)

Lemma transpositionTripartiteTransformation :
  forall (A : Type),
  forall R1 R2 R3 M1 M2,
    @Transformation A (R2 ++ R1 ++ R3) M1 M2
    -> @Transformation A (R1 ++ R2 ++ R3) M1 M2.
Proof.
  intros A.
  fix HR 2.
  intros R1 R2 R3 M1 M2.
  destruct R2 as [ | tR2 rR2].
  {
    simpl.
    tauto.
  }
  {
    intro Equiv.
    replace (R1 ++ (tR2 :: rR2) ++ R3) with ((R1 ++ [tR2]) ++ rR2 ++ R3).
    apply HR.
    replace (rR2 ++ (R1 ++ [tR2]) ++ R3)
      with ((rR2 ++ R1) ++ [tR2] ++ R3).
    eapply (premiereRegle (length (rR2 ++ R1)) tR2).
    simpl.
    rewrite valeurListeConsApresListe.
    simpl.
    f_equal.
    symmetry.
    apply deplierRegle.
    rewrite prefixeGaucheConcatenation.
    replace (suffixe (S (length (rR2 ++ R1))) ((rR2 ++ R1) ++ [tR2] ++ R3))
      with (suffixe (length ((rR2 ++ R1) ++ [tR2]))
                    (((rR2 ++ R1) ++ [tR2]) ++ R3)).
    rewrite suffixeDroiteConcatenation.
    replace (tR2 :: (rR2 ++ R1) ++ R3) with ((tR2 :: rR2) ++ R1 ++ R3).
    assumption.
    egaliteListes.
    f_equal.
    apply longueurListeSingleton.
    egaliteListes.
    egaliteListes.
    egaliteListes.
  }
Qed.

Proposition derniereRegle :
  forall {A : Type},
  forall R M1 M2,
  forall n r,
    valeur n R = [r] ->
    @Transformation A (((prefixe n R) ++ (suffixe (S n) R)) ++ [r]) M1 M2 ->
    @Transformation A R M1 M2.
Proof.
  intros A.
  intros R M1 M2 n r eqR  Transfo.
  rewrite <- (@decompositionListeAvecPivot _ n R).
  replace (prefixe n R ++ valeur n R ++ suffixe (S n) R)
    with ((prefixe n R ++ valeur n R) ++ suffixe (S n) R ++ []).
  apply transpositionTripartiteTransformation.
  replace (suffixe (S n) R ++ (prefixe n R ++ valeur n R) ++ [])
    with (suffixe (S n) R ++ prefixe n R ++ valeur n R).
  apply transpositionTripartiteTransformation.
  rewrite eqR.
  replace (prefixe n R ++ suffixe (S n) R ++ [r])
    with ((prefixe n R ++ suffixe (S n) R) ++ [r]).
  assumption.
  egaliteListes.
  egaliteListes.
  egaliteListes.
Qed.

Arguments derniereRegle {_ _ _ _ _}.

Proposition solutionInerte :
  forall (A : Type),
  forall M1 M2,
    @Transformation A [] M1 M2 -> EquivalenceMoleculaire [M1] M2.
Proof.
  intros A.
  fix HR 3.
  intros M1 M2 HT.
  destruct HT as [ n eqN
                 | _ eqN
                 | n g N1 r N2 eqN 
                 | n T v r1 eqN
                 | n X r2 eqN
                 | r r1 r2 eqN
                 | r r1 r2 eqN
                 | r r1 r2 eqN
                 | n r eqN
                 | n N HTG HTD]; try (assumption || discriminate eqN).
  {
    simpl in HTG.
    simpl in HTD.
    apply transitiviteMoleculaire with N.
    apply HR.
    assumption.
    apply HR.
    assumption.
  }    
Qed.

Proposition TransformationNeutre :
  forall (A:Type),
  forall M1 M2, 
    @Transformation A [neutreRegle] M1 M2 -> @Transformation A [] M1 M2.
Proof.
  intro A.
  fix HR 3; intros.
  destruct H; try(destruct n; simpl in *; discriminate H); try discriminate H.
  {
  destruct n; simpl in *; try discriminate H; trivial.
  }
  {
  destruct n; simpl in *; try discriminate H.
  injection H; intros; subst. apply HR; trivial.
  }
  {
  destruct n; simpl in *.
    {
    apply HR in H0.
    apply solutionInerte in H.
    apply solutionInerte in H0.
    apply (transitiviteMoleculaire _ M1 N M2) in H; trivial.
    apply identiteTransformation; trivial.
    }
    {
    apply HR in H.
    apply solutionInerte in H.
    apply solutionInerte in H0.
    apply (transitiviteMoleculaire _ M1 N M2) in H; trivial.
    apply identiteTransformation; trivial.
    }
  }
Qed.


Proposition compatibiliteEquivalenceMoleculaire_blocage :
  forall (A : Type)(R : list (@Regle A))(M1 M2 : @Molecule A),
    Blocage R M1
    -> EquivalenceMoleculaire [M1] M2
    -> Blocage R M2.
Proof.
  intros A R M1 M2 HB1 EqM.
  intros N HT.
  apply (HB1 N).
  apply compatibiliteEquivalenceMoleculaire_transformation with M2.
  assumption.
  apply symmetrieMoleculaire; assumption.
Qed.


Lemma blocageReactionParRecurrence :
  forall (A : Type)(R : list (@Regle A))(M N : @Molecule A),
    (Transformation R M N)
    -> (exists g M1 M2 r, R = [g ? M1 --o M2 , r] /\  ~(g /\ EquivalenceMoleculaire [M] M1))
    -> False.
Proof.
  fix HR 5.
  intros A R M N HT [g [M1 [M2 [r [egR cond]]]]].
  {
    case HT as [ n egN
               | eqR egN
               | n g' N1 N2 r' egN abs1 cg HT
               | n T v r1 egN
               | n X r2 egN
               | n r1 r2 egN
               | n r1 r2 egN
               | n r1 r2 egN
               | n r' egN
               | n N' HTG HTD].
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in eqR.
      discriminate eqR.
    }
    {
      rewrite egR in abs1, egN.
      case n as [ | pn].
      {
        simpl in egN.
        injection egN.
        intros eqG egN2 eqM2 eqMN1.
        apply cond.
        split.
        rewrite eqG; assumption.
        apply solutionInerte in abs1.
        rewrite eqMN1; assumption.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        apply (HR A (r' :: prefixe 0 R ++ suffixe 1 R) M N).
        assumption.
        exists g, M1, M2, r.
        split.
        rewrite egR.
        simpl.
        simpl in egN.
        symmetry.
        assumption.
        assumption.
      }
      {
        discriminate egN.
      }
    }
    {
      case n as [ | pn].
      {
        apply (HR A (suffixe 0 R) N' N).
        assumption.
        exists g, M1, M2, r.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        rewrite egR in HTG.
        simpl in HTG.
        apply solutionInerte in HTG.
        intro conjGeqM.
        apply cond.
        case conjGeqM as [garde eqM].
        split.
        assumption.
        apply transitiviteMoleculaire with N'; assumption.
      }
      {
        apply (HR A (prefixe (S pn)  R) M N').
        assumption.
        exists g, M1, M2, r.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        assumption.
      }
    }
  }
Qed.

Lemma blocageReaction :
    forall {A : Type}, forall M M1 M2 : (@Molecule A), forall r : Regle, forall g : Prop,
            ~(g /\ EquivalenceMoleculaire [M] M1)
            -> Blocage [g ? M1 --o M2 , r] M.
Proof.
  intros A M M1 M2 r g cond.
  intros N HT.
  apply (blocageReactionParRecurrence A [g ? M1 --o M2, r] M N).
  assumption.
  exists g, M1, M2, r.
  auto.
Qed.

Lemma reciproqueBlocageReaction :
    forall {A : Type}, forall M M1 M2 : (@Molecule A), forall g : Prop,
            Blocage [g ? M1 -o M2] M
            -> ~(g /\ EquivalenceMoleculaire [M] M1).
Proof.
  intros A M M1 M2 g blocage cond.
  case cond as [garde eqM].
  apply (blocage M2).
  apply (reactionTransformation 0 g M1 M2 neutreRegle).
  simpl.
  reflexivity.
  simpl.
  apply identiteTransformation.
  reflexivity.
  assumption.
  assumption.
  simpl.
  apply neutreTransformation with 0.
  simpl.
  reflexivity.
  simpl.
  apply identiteTransformation.
  reflexivity.
  apply reflexiviteMoleculaire.
Qed.

Lemma blocageReactionAvecContinuationParRecurrence :
  forall (A : Type)(R : list (@Regle A))(M N : @Molecule A),
    (Transformation R M N)
    -> (exists g M1 M2 r, R = [g ? M1 --o M2 , r]
                          /\  ~(g /\ EquivalenceMoleculaire [M] M1
                                /\ exists Nr,  Transformation [r] M2 Nr))
    -> False.
Proof.
  fix HR 5.
  intros A R M N HT [g [M1 [M2 [r [egR cond]]]]].
  {
    case HT as [ n egN
               | eqR egN
               | n g' N1 N2 r' egN abs1 cg HT
               | n T v r1 egN
               | n X r2 egN
               | n r1 r2 egN
               | n r1 r2 egN
               | n r1 r2 egN
               | n r' egN
               | n N' HTG HTD].
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in eqR.
      discriminate eqR.
    }
    {
      rewrite egR in abs1, egN.
      case n as [ | pn].
      {
        simpl in egN.
        injection egN.
        intros eqG egr eqMN2 eqMN1.
        apply cond.
        split.
        rewrite eqG; assumption.
        split.
        apply solutionInerte in abs1.
        rewrite eqMN1; assumption.
        exists N.
        rewrite eqMN2.
        rewrite egr.
        rewrite egR in HT.        
        simpl in HT.
        assumption.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        apply (HR A (r' :: prefixe 0 R ++ suffixe 1 R) M N).
        assumption.
        exists g, M1, M2, r.
        split.
        rewrite egR.
        simpl.
        simpl in egN.
        symmetry.
        assumption.
        assumption.
      }
      {
        discriminate egN.
      }
    }
    {
      case n as [ | pn].
      {
        apply (HR A (suffixe 0 R) N' N).
        assumption.
        exists g, M1, M2, r.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        rewrite egR in HTG.
        simpl in HTG.
        apply solutionInerte in HTG.
        intro conjGeqM.
        apply cond.
        case conjGeqM as [garde [eqM HTr]].
        split.
        assumption.
        split.
        apply transitiviteMoleculaire with N'; assumption.
        assumption.
      }
      {
        apply (HR A (prefixe (S pn)  R) M N').
        assumption.
        exists g, M1, M2, r.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        assumption.
      }
    }
  }
Qed.

Lemma blocageReactionAvecContinuation :
    forall {A : Type}, forall M M1 M2 : (@Molecule A), forall r : Regle, forall g : Prop,
            ~(g /\ EquivalenceMoleculaire [M] M1 /\ exists Nr,  Transformation [r] M2 Nr)
            -> Blocage [g ? M1 --o M2 , r] M.
Proof.
  intros A M M1 M2 r g cond.
  intros N HT.
  apply (blocageReactionAvecContinuationParRecurrence A [g ? M1 --o M2, r] M N).
  assumption.
  exists g, M1, M2, r.
  auto.
Qed.

Lemma reciproqueBlocageReactionAvecContinuation :
    forall {A : Type}, forall M M1 M2 : (@Molecule A), forall r : Regle, forall g : Prop,
            Blocage [g ? M1 --o M2, r] M
            -> ~(g /\ EquivalenceMoleculaire [M] M1 /\ exists Nr,  Transformation [r] M2 Nr).
Proof.
  intros A M M1 M2 r g blocage cond.
  case cond as [garde [eqM [Nr HTr]]].
  apply (blocage Nr).
  apply (reactionTransformation 0 g M1 M2 r).
  simpl.
  reflexivity.
  simpl.
  apply identiteTransformation.
  reflexivity.
  assumption.
  assumption.
  simpl.
  assumption.
Qed.


Lemma blocageQuantificationValeurParRecurrence :
  forall (A : Type)(R : list (@Regle A))(M N : @Molecule A),
    (Transformation R M N)
    -> (exists (T : Type)(r : T -> (@Regle A)),
           R = [∀1 r]
           /\  (forall v : T, Blocage [r v] M))
    -> False.
Proof.
  fix HR 5.
  intros A R M N HT [T [r [egR cond]]].
  {
    case HT as [ n egN
               | eqR egN
               | n g' N1 N2 r' egN abs1 cg HT
               | n T' v' r1 egN
               | n X r2 egN
               | n r1 r2 egN
               | n r1 r2 egN
               | n r1 r2 egN
               | n r' egN
               | n N' HTG HTD].
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in eqR.
      discriminate eqR.
    }
    {
      rewrite egR in abs1, egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        rewrite egR in HT.
        simpl in HT.
        apply teteFonctionnelle in egN.
        apply eq_sym in egN.
        case (projectionEgaliteFonctionQuantificationValeur_constructif
                A  (∀1 r1) (∀1 r) v' egN) as [egT egV].
        simpl in egT, egV.
        apply (cond (conversion v' egT) N).
        rewrite <- egV.
        assumption.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        apply (HR A (r' :: prefixe 0 R ++ suffixe 1 R) M N).
        assumption.
        exists T, r.
        split.
        rewrite egR.
        simpl.
        simpl in egN.
        symmetry.
        assumption.
        assumption.
      }
      {
        discriminate egN.
      }
    }
    {
      case n as [ | pn].
      {
        apply (HR A (suffixe 0 R) N' N).
        assumption.
        exists T, r.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        rewrite egR in HTG.
        simpl in HTG.
        apply solutionInerte in HTG.
        intros v N2 HT.
        apply (compatibiliteEquivalenceMoleculaire_blocage A [r v] M N' (cond v) HTG N2).
        assumption.
      }
      {
        apply (HR A (prefixe (S pn)  R) M N').
        assumption.
        exists T, r.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        assumption.
      }
    }
  }
Qed.

Lemma blocageQuantificationValeur :
    forall {A : Type}, forall M : (@Molecule A), forall (T : Type)(r : T -> (@Regle A)),
          (forall v : T, Blocage [r v] M)
          -> Blocage [∀1 r] M.
Proof.
  intros A M T r cond.
  intros N HT.
  apply (blocageQuantificationValeurParRecurrence A [∀1 r] M N).
  assumption.
  exists T, r.
  auto.
Qed.

Lemma reciproqueBlocageQuantificationValeur :
    forall {A : Type}, forall M : (@Molecule A), forall (T : Type)(r : T -> (@Regle A)),
          Blocage [∀1 r] M
          -> (forall v : T, Blocage [r v] M).
Proof.
  intros A M T r HB v N HT.
  apply (HB N).
  apply (instanciationValeur 0 v r).
  reflexivity.
  simpl.
  assumption.
Qed.

Lemma blocageQuantificationMoleculeParRecurrence :
  forall (A : Type)(R : list (@Regle A))(M N : @Molecule A),
    (Transformation R M N)
    -> (exists (r : Molecule -> (@Regle A)),
           R = [∀2 r]
           /\  (forall X, Blocage [r X] M))
    -> False.
Proof.
  fix HR 5.
  intros A R M N HT [r [egR cond]].
  {
    case HT as [ n egN
               | eqR egN
               | n g' N1 N2 r' egN abs1 cg HT
               | n T' v' r1 egN
               | n X r2 egN
               | n r1 r2 egN
               | n r1 r2 egN
               | n r1 r2 egN
               | n r' egN
               | n N' HTG HTD].
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in eqR.
      discriminate eqR.
    }
    {
      rewrite egR in abs1, egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        rewrite egR in HT.
        simpl in HT.
        injection egN.
        intro egQ.
        apply (cond X N).
        rewrite egQ.
        assumption.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        apply (HR A (r' :: prefixe 0 R ++ suffixe 1 R) M N).
        assumption.
        exists r.
        split.
        rewrite egR.
        simpl.
        simpl in egN.
        symmetry.
        assumption.
        assumption.
      }
      {
        discriminate egN.
      }
    }
    {
      case n as [ | pn].
      {
        apply (HR A (suffixe 0 R) N' N).
        assumption.
        exists r.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        rewrite egR in HTG.
        simpl in HTG.
        apply solutionInerte in HTG.
        intros X N2 HT.
        apply (compatibiliteEquivalenceMoleculaire_blocage A [r X] M N' (cond X) HTG N2).
        assumption.
      }
      {
        apply (HR A (prefixe (S pn)  R) M N').
        assumption.
        exists r.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        assumption.
      }
    }
  }
Qed.

Lemma blocageQuantificationMolecule :
    forall {A : Type}, forall (M : (@Molecule A))(r : @Molecule A -> (@Regle A)),
          (forall X, Blocage [r X] M)
          -> Blocage [∀2 r] M.
Proof.
  intros A M r cond.
  intros N HT.
  apply (blocageQuantificationMoleculeParRecurrence A [∀2 r] M N).
  assumption.
  exists r.
  auto.
Qed.

Lemma reciproqueBlocageQuantificationMolecule :
  forall {A : Type}, forall (M : (@Molecule A))(r : @Molecule A -> (@Regle A)),
      Blocage [∀2 r] M
      -> (forall X, Blocage [r X] M).
Proof.
  intros A M r HB X N HT.
  apply (HB N).
  apply (instanciationMolecule 0 X r).
  reflexivity.
  simpl.
  assumption.
Qed.

Lemma blocageConjonctionAdditiveParRecurrence :
  forall (A : Type)(R : list (@Regle A))(M N : @Molecule A),
    (Transformation R M N)
    -> (exists (r1 r2 : @Regle A),
           R = [r1 ∧ r2]
           /\  (Blocage [r1] M) /\ (Blocage [r2] M))
    -> False.
Proof.
  fix HR 5.
  intros A R M N HT [r1 [r2 [egR [HB1 HB2]]]].
  {
    case HT as [ n egN
               | eqR egN
               | n g N1 N2 r egN abs1 cg HT
               | n T' v' r egN
               | n X r egN
               | n r1' r2' egN
               | n r1' r2' egN
               | n r1' r2' egN
               | n r egN
               | n N' HTG HTD].
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in eqR.
      discriminate eqR.
    }
    {
      rewrite egR in abs1, egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        injection egN.
        intros eg_r2 eg_r1.
        rewrite egR in HT.
        simpl in HT.
        apply (HB1 N).
        rewrite eg_r1.
        assumption.
      }
      {
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        injection egN.
        intros eg_r2 eg_r1.
        rewrite egR in HT.
        simpl in HT.
        apply (HB2 N).
        rewrite eg_r2.
        assumption.
      }
      {
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        apply (HR A (r :: prefixe 0 R ++ suffixe 1 R) M N).
        assumption.
        exists r1, r2.
        split.
        rewrite egR.
        simpl.
        simpl in egN.
        symmetry.
        assumption.
        split; assumption.
      }
      {
        discriminate egN.
      }
    }
    {
      case n as [ | pn].
      {
        apply (HR A (suffixe 0 R) N' N).
        assumption.
        exists r1, r2.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        rewrite egR in HTG.
        simpl in HTG.
        apply solutionInerte in HTG.
        split.
        apply (compatibiliteEquivalenceMoleculaire_blocage A [r1] M N' HB1 HTG).
        apply (compatibiliteEquivalenceMoleculaire_blocage A [r2] M N' HB2 HTG).
      }
      {
        apply (HR A (prefixe (S pn)  R) M N').
        assumption.
        exists r1, r2.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        auto.
      }
    }
  }
Qed.


Lemma blocageConjonctionAdditive :
    forall {A : Type}, forall (M : (@Molecule A))(r1 r2 : @Regle A),
          ((Blocage [r1] M) /\ (Blocage [r2] M))
          -> Blocage [r1 ∧ r2] M.
Proof.
  intros A M r1 r2 cond.
  intros N HT.
  apply (blocageConjonctionAdditiveParRecurrence A [r1 ∧ r2] M N).
  assumption.
  exists r1, r2.
  auto.
Qed.

Lemma reciproqueBlocageConjonctionAdditive :
  forall {A : Type}, forall (M : (@Molecule A))(r1 r2 : @Regle A),
      Blocage [r1 ∧ r2] M
      -> ((Blocage [r1] M) /\ (Blocage [r2] M)).
Proof.
  intros A M r1 r2 HB.
  split.
  intros N HT.
  apply (HB N).
  apply (conjonctionAdditiviteGaucheTransformation 0 r1 r2).
  reflexivity.
  simpl.
  assumption.
  intros N HT.
  apply (HB N).
  apply (conjonctionAdditiviteDroiteTransformation 0 r1 r2).
  reflexivity.
  simpl.
  assumption.
Qed.

Lemma blocageConjonctionMultiplicativeParRecurrence :
  forall (A : Type)(R : list (@Regle A))(M N : @Molecule A),
    (Transformation R M N)
    -> (exists (r1 r2 : @Regle A),
           R = [r1 ⊠ r2]
           /\  (Blocage [r1; r2] M))
    -> False.
Proof.
  fix HR 5.
  intros A R M N HT [r1 [r2 [egR HB]]].
  {
    case HT as [ n egN
               | eqR egN
               | n g N1 N2 r egN abs1 cg HT
               | n T' v' r egN
               | n X r egN
               | n r1' r2' egN
               | n r1' r2' egN
               | n r1' r2' egN
               | n r egN
               | n N' HTG HTD].
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in eqR.
      discriminate eqR.
    }
    {
      rewrite egR in abs1, egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        simpl in egN.
        discriminate egN.
      }
      {
        simpl in egN.
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        injection egN.
        intros eg_r2 eg_r1.
        rewrite egR in HT.
        simpl in HT.
        apply (HB N).
        rewrite eg_r1.
        rewrite eg_r2.
        assumption.
      }
      {
        discriminate egN.
      }
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn]; try (discriminate egN).
    }
    {
      rewrite egR in egN.
      case n as [ | pn].
      {
        apply (HR A (r :: prefixe 0 R ++ suffixe 1 R) M N).
        assumption.
        exists r1, r2.
        split.
        rewrite egR.
        simpl.
        simpl in egN.
        symmetry.
        assumption.
        assumption.
      }
      {
        discriminate egN.
      }
    }
    {
      case n as [ | pn].
      {
        apply (HR A (suffixe 0 R) N' N).
        assumption.
        exists r1, r2.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        rewrite egR in HTG.
        simpl in HTG.
        apply solutionInerte in HTG.
        apply (compatibiliteEquivalenceMoleculaire_blocage A [r1; r2] M N' HB HTG).
      }
      {
        apply (HR A (prefixe (S pn)  R) M N').
        assumption.
        exists r1, r2.
        split.
        rewrite egR.
        simpl.
        reflexivity.
        auto.
      }
    }
  }
Qed.

Lemma blocageConjonctionMultiplicative :
    forall {A : Type}, forall (M : (@Molecule A))(r1 r2 : @Regle A),
          (Blocage [r1; r2] M)
          -> Blocage [r1 ⊠ r2] M.
Proof.
  intros A M r1 r2 cond.
  intros N HT.
  apply (blocageConjonctionMultiplicativeParRecurrence A [r1 ⊠ r2] M N).
  assumption.
  exists r1, r2.
  auto.
Qed.

Lemma reciproqueBlocageConjonctionMultiplicative :
  forall {A : Type}, forall (M : (@Molecule A))(r1 r2 : @Regle A),
      (Blocage [r1 ⊠ r2] M)
      -> (Blocage [r1; r2] M). 
Proof.
  intros A M r1 r2 HB.
  intros N HT.
  apply (HB N).
  apply (conjonctionMultiplicativeTransformation 0 r1 r2).
  reflexivity.
  simpl.
  assumption.
Qed.

(* TODO blocage / liste de règles et non plus seulement un singleton ?
 * La négation d'un type inductif correspond à un type co-inductif.
 * Objectif : définir le blocage par une proposition co-inductive et 
 * montrer l'équivalence avec la définition par une négation.
*)












































