Require Export prefixes_suffixes.

Import ListNotations.

(* Lemme technique à appeler via une tactique idéalement *)

Lemma simplificationCoupleListeX :
  forall {T X: Type},
  forall t : T,
  forall x (y : X) x' (y' : X),
    (x, y) = (x', y') -> (t :: x, y) = (t :: x', y').
Proof.
  intros T X t x y x' y' eq.
  injection eq.
  intros eqY eqX.
  rewrite eqX.
  rewrite eqY.
  reflexivity.
Qed.

(* Préfixes & Suffixes *)

Proposition equivalenceDefinitionsPrefixe :
  forall T: Type,
  forall n (l : list T),
    prefixeRC l (VAL n) = (prefixe n l, VAL (n - length l)).
Proof.
  intro T.
  fix HR 2.
  intros n l.
  destruct l as [ | tl rl ].
  {
    simpl.
    rewrite <- Minus.minus_n_O.
    reflexivity.
  }
  {
    destruct n as [ | pn ].
    {
      simpl.
      reflexivity.
    }
    {
      simpl.
      apply simplificationCoupleListeX.
      rewrite <- surjective_pairing.
      apply HR.
    }
  }
Qed.

Proposition equivalenceDefinitionsPrefixeListe :
  forall T: Type,
  forall n (l : list T),
    fst (prefixeRC l (VAL n)) = prefixe n l.
Proof.
  intros T n l.
  rewrite equivalenceDefinitionsPrefixe.
  reflexivity.
Qed.  
  
Proposition equivalenceDefinitionsSuffixe :
  forall T: Type,
  forall n (l : list T),
    suffixeRC l (VAL n) = (suffixe n l, VAL (n - length l)).
Proof.
  intro T.
  fix HR 2.
  intros n l.
  destruct l as [ | tl rl ].
  {
    simpl.
    rewrite <- Minus.minus_n_O.
    reflexivity.
  }
  {
    destruct n as [ | pn ].
    {
      simpl.
      reflexivity.
    }
    {
      simpl.
      apply HR.
    }
  }
Qed.

Proposition equivalenceDefinitionsSuffixeListe :
  forall T: Type,
  forall n (l : list T),
    fst (suffixeRC l (VAL n)) = suffixe n l.
Proof.
  intros T n l.
  rewrite equivalenceDefinitionsSuffixe.
  reflexivity.
Qed.  

Proposition prefixeEnZero :
  forall T,
  forall (l : list T),
    prefixe 0 l = [].
Proof.
  intros T l.
  destruct l; reflexivity.
Qed.  

Proposition prefixeEnZeroRC :
  forall T,
  forall (l : list T),
    prefixeRC l (VAL 0) = ([], VAL 0).
Proof.
  intros T l.
  rewrite equivalenceDefinitionsPrefixe.
  rewrite prefixeEnZero.
  reflexivity.
Qed.  

Proposition suffixeEnZero :
  forall T,
  forall (l : list T),
    suffixe 0 l = l.
Proof.
  intros T l.
  destruct l; reflexivity.
Qed.  

Proposition suffixeEnZeroRC :
  forall T,
  forall (l : list T),
    suffixeRC l (VAL 0) = (l, VAL 0).
Proof.
  intros T l.
  rewrite equivalenceDefinitionsSuffixe.
  rewrite suffixeEnZero.
  reflexivity.
Qed.  

Proposition prefixeEnFin :
  forall T,
  forall (l : list T),
    prefixe (length l) l = l.
Proof.
  intro T.
  fix HR 1.
  intro l.
  destruct l as [ | tl rl].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    f_equal.
    apply HR.
  }  
Qed.  

Proposition prefixeEnFinRC :
  forall T,
  forall (l : list T),
    prefixeRC l (VAL (length l)) = (l, VAL 0).
Proof.
  intros T l.
  rewrite equivalenceDefinitionsPrefixe.
  rewrite prefixeEnFin.
  rewrite PeanoNat.Nat.sub_diag.
  reflexivity.
Qed.  

Proposition prefixeComplet :
  forall T,
  forall (l : list T),
  forall t,
    length l - t = 0
    -> prefixe t l = l.
Proof.
  intro T.
  fix HR 1.
  intros l t eqT.
  destruct l as [ | tl rl].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    simpl in eqT.
    destruct t as [ | pt].
    discriminate eqT.
    f_equal.
    apply HR.
    assumption.
  }  
Qed.  

Proposition prefixeCompletRC :
  forall T,
  forall (l : list T),
  forall t,
    length l - t = 0
    -> prefixeRC l (VAL t) = (l, VAL (t - length l)).
Proof.
  intros T l t eqT.
  rewrite equivalenceDefinitionsPrefixe.
  rewrite prefixeComplet.
  reflexivity.
  assumption.
Qed.

Proposition suffixeEnFin :
  forall T,
  forall (l : list T),
    suffixe (length l) l = [].
Proof.
  intro T.
  fix HR 1.
  intro l.
  destruct l as [ | tl rl].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    apply HR.
  }  
Qed.  

Proposition suffixeEnFinRC :
  forall T,
  forall (l : list T),
    suffixeRC l (VAL (length l)) = ([], VAL 0).
Proof.
  intros T l.
  rewrite equivalenceDefinitionsSuffixe.
  rewrite suffixeEnFin.
  rewrite PeanoNat.Nat.sub_diag.
  reflexivity.
Qed.  

Proposition suffixeVide :
  forall T,
  forall (l : list T),
  forall t,
    length l - t = 0
    -> suffixe t l = [].
Proof.
  intro T.
  fix HR 1.
  intros l t eqT.
  destruct l as [ | tl rl].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    simpl in eqT.
    destruct t as [ | pt].
    discriminate eqT.
    apply HR.
    assumption.
  }  
Qed.  

Proposition suffixeVideRC :
  forall T,
  forall (l : list T),
  forall t,
    length l - t = 0
    -> suffixeRC l (VAL t) = ([], VAL (t - length l)).
Proof.
  intros T l t eqT.
  rewrite equivalenceDefinitionsSuffixe.
  rewrite suffixeVide.
  reflexivity.
  assumption.
Qed.

(* Sous-Listes *)

Proposition equivalenceDefinitionsSousListe : 
  forall T: Type,
  forall n d (l : list T),
    sousListeRF l (PLAGE n d)
    = (sousListe n d l, PLAGE (n - length l) (d + n - length l - (n - length l))).
Proof.
  intro T.
  fix HR 3.
  intros n d l.
  destruct l as [ | tl rl].
  {
    simpl.
    rewrite <- Minus.minus_n_O.
    rewrite <- Minus.minus_n_O.
    rewrite PeanoNat.Nat.add_sub.
    reflexivity.
  }
  {
    destruct n as [ | pn].
    {
      destruct d as [ | pd].
      {
        simpl.
        reflexivity.
      }
      {
        simpl.
        apply simplificationCoupleListeX.
        rewrite <- surjective_pairing.
        apply HR.
      }
    }
    {
      simpl.
      replace (d + S pn - S (length rl) - (pn - length rl))
        with (d + pn - length rl - (pn - length rl)).      
      apply (HR pn d rl).
      replace (d + S pn) with (S (d + pn)).
      simpl.
      reflexivity.
      transitivity (S pn + d).
      simpl.
      f_equal.
      apply PeanoNat.Nat.add_comm.
      apply PeanoNat.Nat.add_comm.
    }
  }
Qed.  

Proposition equivalenceDefinitionsSousListeListe : 
  forall T: Type,
  forall n d (l : list T),
    fst (sousListeRF l (PLAGE n d))
    = sousListe n d l.
Proof.
  intros T n d l.
  rewrite equivalenceDefinitionsSousListe.
  simpl.
  reflexivity.
Qed.

Proposition sousListeEnFin :
  forall T,
  forall (l : list T),
  forall d,
    sousListe (length l) d l = [].
Proof.
  intro T.
  fix HR 1.
  intros l d.
  destruct l as [ | tl rl].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    apply HR.
  }  
Qed.  

Proposition sousListeEnFinRF :
  forall T,
  forall (l : list T),
  forall d,
    sousListeRF l (PLAGE (length l) d) = ([], PLAGE 0 d).
Proof.
  intros T l d.
  rewrite equivalenceDefinitionsSousListe.
  rewrite sousListeEnFin.
  rewrite PeanoNat.Nat.sub_diag.
  rewrite PeanoNat.Nat.sub_0_r.
  f_equal.
  f_equal.
  symmetry.
  apply simplificationDroiteAddition.
  reflexivity.
Qed.  

Proposition sousListeEnZero :
  forall T,
  forall l : list T,
  forall n,
    sousListe 0 n  l = prefixe n l.
Proof.
  intro T.
  fix HR 1.
  intros l n.
  destruct l as [ | tl rl].
  {
    simpl.
    reflexivity.
  }
  {
    destruct n as [ | pn].
    {
      simpl.
      reflexivity.
    }
    {
      simpl.
      f_equal.
      apply HR.
    }
  }
Qed.

Proposition sousListeEnZeroRF :
  forall T,
  forall l : list T,
  forall n,
    sousListeRF l (PLAGE 0 n) = (prefixe n l, PLAGE 0 (n - length l)).
Proof.
  intros T l d.
  rewrite equivalenceDefinitionsSousListe.
  simpl.
  rewrite sousListeEnZero.
  rewrite PeanoNat.Nat.sub_0_r.
  rewrite PeanoNat.Nat.add_0_r.
  reflexivity.
Qed.  

Proposition sousListeVide :
  forall T,
  forall (l : list T),
  forall t d,
    length l - t = 0
    -> sousListe t d l = [].
Proof.
  intro T.
  fix HR 1.
  intros l t d eqT.
  destruct l as [ | tl rl].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    simpl in eqT.
    destruct t as [ | pt].
    discriminate eqT.
    apply HR.
    assumption.
  }  
Qed.  

Proposition sousListeVideRC :
  forall T,
  forall (l : list T),
  forall t d,
    length l - t = 0
    -> sousListeRF l (PLAGE t d) = ([], PLAGE (t - length l) d).
Proof.
  intros T l t d eqT.
  rewrite equivalenceDefinitionsSousListe.
  replace (t + d) with (d + t).
  replace (d + t - length l - (t - length l)) with d.
  rewrite sousListeVide.  
  reflexivity.
  assumption.
  apply simplificationDroiteAddition.
  destruct (simplificationDroiteOpposeSoustractionNulle _ _ eqT) as [d' eqD'].
  apply simplificationDroiteAddition.
  apply eq_sym in eqD'.
  symmetry.
  transitivity (d + d' + length l).
  rewrite <- eqD'.
  rewrite Plus.plus_assoc_reverse.
  reflexivity.
  apply simplificationDroiteAddition in eqD'.
  rewrite <- eqD'.
  reflexivity.
  apply PeanoNat.Nat.add_comm.
Qed.

(* Valeur *)

Proposition valeurEnZero :
  forall {T : Type},
  forall l : list T,
  forall t : T,
    valeur 0 (t :: l) = [t].
Proof.
  intros T l t.
  unfold valeur.
  simpl.
  rewrite sousListeEnZero.
  rewrite prefixeEnZero.
  reflexivity.
Qed.

(* Concatenation *)

Proposition equivalenceDefinitionConcatenationR :
  forall V T,
  forall (rl1 rl2 : Reglage V (list T)),
  forall v,
    concatenationMonadiqueR rl1 rl2 v = concatenationR rl1 rl2 v.
Proof.
  intros V T.
  intros rl1 rl2 v.
  compute.
  reflexivity.
Qed.

Proposition prefixeRCMorphisme :
  forall T,
  forall l1 l2 : list T,
  forall I,
    prefixeRC (l1 ++ l2) I
    =
    concatenationR (prefixeRC l1) (prefixeRC l2) I.
Proof.
  intro T.
  fix HR 1.
  intros l1 l2 c.
  destruct l1 as [ | tl1 rl1].
  {
    simpl.
    unfold concatenationR.
    simpl.
    apply surjective_pairing.
  }
  {
    destruct c as [[ | pn]].
    {
      simpl.
      unfold concatenationR.
      simpl.
      rewrite prefixeEnZeroRC.
      apply surjective_pairing.
    }
    {
      simpl.
      unfold concatenationR.
      simpl.
      apply simplificationCoupleListeX.
      rewrite <- surjective_pairing.
      transitivity (concatenationR (prefixeRC rl1) (prefixeRC l2) (VAL pn)).
      apply HR.
      unfold concatenationR.
      reflexivity.
    }
  }
Qed.

Proposition suffixeRCMorphisme :
  forall T,
  forall l1 l2 : list T,
  forall I,
    suffixeRC (l1 ++ l2) I
    =
    concatenationR (suffixeRC l1) (suffixeRC l2) I.
Proof.
  intro T.
  fix HR 1.
  intros l1 l2 c.
  destruct l1 as [ | tl1 rl1].
  {
    simpl.
    unfold concatenationR.
    simpl.
    apply surjective_pairing.
  }
  {
    destruct c as [[ | pn]].
    {
      simpl.
      unfold concatenationR.
      simpl.
      rewrite suffixeEnZeroRC.
      simpl.
      reflexivity.
    }
    {
      simpl.
      unfold concatenationR.
      transitivity (concatenationR (suffixeRC rl1) (suffixeRC l2) (VAL pn)).
      apply HR.
      unfold concatenationR.
      reflexivity.
    }
  }
Qed.

Proposition sousListeRFMorphisme :
  forall T,
  forall l1 l2 : list T,
  forall f,
    sousListeRF (l1 ++ l2) f
    =
    concatenationR (sousListeRF l1) (sousListeRF l2) f.
Proof.
  intro T.
  fix HR 1.
  intros l1 l2 f.
  destruct l1 as [ | tl1 rl1].
  {
    simpl.
    unfold concatenationR.
    simpl.
    apply surjective_pairing.
  }
  {
    destruct f as [[ | pn] d] eqn:cas.
    {
      destruct d as [ | pd].
      {
        simpl.
        unfold concatenationR.
        simpl.
        rewrite sousListeEnZeroRF.
        rewrite prefixeEnZero.
        simpl.
        reflexivity.
      }
      {
        simpl.
        unfold concatenationR.
        simpl.
        apply simplificationCoupleListeX.
        rewrite <- surjective_pairing.
        apply HR.
      }
    }
    {
      simpl.
      apply HR.
    }
  }
Qed.

Proposition valeurEnFin :
  forall {T : Type},
  forall l : list T,
  forall t : T,
    valeur (length l) (l ++ [t]) = [t].
Proof.
  intros T l t.
  unfold valeur.
  simpl.
  rewrite <- equivalenceDefinitionsSousListeListe.
  rewrite sousListeRFMorphisme.
  simpl.
  rewrite sousListeEnFinRF.
  simpl.
  reflexivity.
Qed.

Proposition decompositionListe :
  forall T, forall n, forall l : list T,
        prefixe n l ++ suffixe n l = l.
Proof.
  intro T.
  fix HR 2.
  intros n l.
  destruct l as [ | tl rl].
  {
    reflexivity.
  }
  {
    destruct n as [ | pn].
    {
      simpl.
      reflexivity.
    }
    {
      simpl.
      f_equal.
      apply HR.      
    }
  }
Qed.


Proposition decompositionListeAvecPivot :
  forall T, forall n, forall l : list T, 
        prefixe n l
                ++ valeur n l
                ++ suffixe (S n) l
        = l.
Proof.
  intros T.
  fix HR 2.
  intros n l.
  destruct l as [ | tl rl].
  {
    simpl.
    reflexivity.
  }
  {
    simpl.
    unfold valeur.
    simpl.
    destruct n as [ | pn].
    {
      simpl.
      rewrite suffixeEnZero.
      rewrite sousListeEnZero.
      rewrite prefixeEnZero.
      reflexivity.
    }
    {
      simpl.
      f_equal.
      apply HR.
    }
  }
Qed.

(** Tactiques *)

Ltac distributionSousListePremisse H :=
  rewrite <- equivalenceDefinitionsSousListeListe in H;
  rewrite sousListeRFMorphisme in H;
  simpl in H;
  rewrite equivalenceDefinitionsSousListe in H.

Ltac distributionSousListeConclusion :=
  rewrite <- equivalenceDefinitionsSousListeListe;
  rewrite sousListeRFMorphisme;
  simpl;
  rewrite equivalenceDefinitionsSousListe.

Ltac distributionValeurPremisse H :=
  unfold valeur in H;
  distributionSousListePremisse H.

Ltac distributionValeurConclusion :=
  unfold valeur;
  distributionSousListeConclusion.


Ltac distributionPrefixePremisse H :=
  rewrite <- equivalenceDefinitionsPrefixeListe in H;
  rewrite prefixeRCMorphisme in H;
  simpl in H;
  rewrite equivalenceDefinitionsPrefixe in H.

Ltac distributionPrefixeConclusion :=
  rewrite <- equivalenceDefinitionsPrefixeListe;
  rewrite prefixeRCMorphisme;
  simpl;
  rewrite equivalenceDefinitionsPrefixe.

Ltac distributionSuffixePremisse H :=        
  rewrite <- equivalenceDefinitionsSuffixeListe in H;
  rewrite suffixeRCMorphisme in H;
  simpl in H;
  rewrite equivalenceDefinitionsSuffixe in H.

Ltac distributionSuffixeConclusion :=
  rewrite <- equivalenceDefinitionsSuffixeListe;
  rewrite suffixeRCMorphisme;
  simpl;
  rewrite equivalenceDefinitionsSuffixe.
  
(* Décomposition avec pivots *)

(* Lemmes utiles *)

Lemma prefixeGaucheConcatenation:
  forall T, forall (l1 l2 : list T),
      prefixe (length l1) (l1 ++ l2) = l1.
Proof.
  intros T l1 l2.
  distributionPrefixeConclusion.
  simpl.
  rewrite prefixeEnFin.
  rewrite PeanoNat.Nat.sub_diag.
  rewrite prefixeEnZeroRC.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma suffixeDroiteConcatenation:
  forall T, forall (l1 l2 : list T),
      suffixe (length l1) (l1 ++ l2) = l2.
Proof.
  intros T l1 l2.
  distributionSuffixeConclusion.
  simpl.
  rewrite suffixeEnFin.
  rewrite PeanoNat.Nat.sub_diag.
  rewrite suffixeEnZeroRC.
  simpl.
  reflexivity.
Qed.

Lemma valeurListeConsApresListe :
  forall T, forall (l : list T) (e : T) (k : list T),
      valeur (length l) (l ++ e :: k) = [e].
Proof.
  intros T l e k.
  distributionValeurConclusion.
  rewrite PeanoNat.Nat.sub_diag.
  rewrite PeanoNat.Nat.sub_0_r.
  rewrite <- (simplificationDroiteAddition 1 (length l) _).
  simpl.
  rewrite sousListeEnFin.
  simpl.
  rewrite sousListeEnZeroRF.
  simpl.
  rewrite prefixeEnZero.
  reflexivity.
  reflexivity.
Qed.

Lemma longeurPrefixe :
  forall T : Type,
  forall l : list T,
  forall n,
    n - length l = 0
    -> length (prefixe n l) = n.
Proof.
  intro T.
  fix HR 1.
  intros l n H.
  destruct l as [ | tl rl].
  {
    simpl.
    simpl in H.
    symmetry.
    rewrite PeanoNat.Nat.sub_0_r in H.
    assumption.
  }
  {
    destruct n as [ | pn].
    {
      simpl.
      reflexivity.
    }
    {
      simpl.
      f_equal.
      apply HR.
      simpl in H.
      assumption.
    }
  }
Qed.

(* Listes bipartites *)

Lemma valeurAvantListeBipartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T),
      (S n) - length l1 = 0
      -> valeur n (l1 ++ l2) = valeur n l1.
Proof.
  intros n T l1 l2 H.
  assert(n - length l1 = 0) as H'.
  {
    destruct (simplificationDroiteOpposeSoustractionNulle _ _ H) as [d eqSn].
    rewrite <- PeanoNat.Nat.add_succ_comm in eqSn.
    symmetry.
    apply opposeSimplificationDroiteAddition with (S d).
    symmetry.
    assumption.
  }    
  distributionValeurConclusion.
  rewrite H'.
  rewrite PeanoNat.Nat.sub_0_r.
  replace (1 + n) with (S n).
  rewrite H.
  simpl.
  rewrite sousListeEnZeroRF.
  rewrite prefixeEnZero.
  simpl.
  rewrite app_nil_r.
  reflexivity.
  reflexivity.
Qed.

Lemma valeurApresListeBipartiteDiff :
  forall d : nat,
  forall T, forall (l1 l2 : list T),
      valeur (d + length l1) (l1 ++ l2) = valeur d l2.
Proof.
  intros d T l1 l2.
  distributionValeurConclusion.
  rewrite sousListeVide.
  replace (d + length l1 - length l1) with d.
  replace (1 + (d + length l1) - length l1 - d) with 1.
  simpl.
  rewrite equivalenceDefinitionsSousListe.  
  simpl.
  reflexivity.
  apply simplificationDroiteAddition.
  apply simplificationDroiteAddition.
  rewrite Plus.plus_assoc_reverse.
  reflexivity.
  apply simplificationDroiteAddition.
  reflexivity.
  symmetry.
  apply opposeSimplificationDroiteAddition with d.
  reflexivity.
Qed.

Lemma valeurApresListeBipartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T),
      length l1 - n = 0
      -> valeur n (l1 ++ l2) = valeur (n - length l1) l2.
Proof.
  intros n T l1 l2 H.
  distributionValeurConclusion.
  destruct (simplificationDroiteOpposeSoustractionNulle _ _ H) as [d eqD].
  apply eq_sym in eqD.
  rewrite <- (simplificationDroiteAddition _ _ _ eqD).
  replace (1 + n - length l1 - d) with 1.
  rewrite sousListeVide.
  simpl.
  rewrite equivalenceDefinitionsSousListe.  
  simpl.
  reflexivity.
  assumption.
  apply simplificationDroiteAddition.
  apply simplificationDroiteAddition.
  rewrite Plus.plus_assoc_reverse.
  rewrite eqD; reflexivity.
Qed.


Lemma prefixeAvantListeBipartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T),
      n - length l1 = 0
      -> prefixe n (l1 ++ l2) = prefixe n l1.
Proof.
  intros n T l1 l2 H.
  distributionPrefixeConclusion.
  rewrite H.
  simpl.
  rewrite prefixeEnZeroRC.
  rewrite app_nil_r.
  reflexivity.
Qed.


Lemma prefixeApresListeBipartiteDiff :
  forall d : nat,
  forall T, forall (l1 l2 : list T),
      prefixe (d + length l1) (l1 ++ l2) = l1 ++ prefixe d l2.
Proof.
  intros d T l1 l2.
  distributionPrefixeConclusion.
  rewrite prefixeComplet.
  rewrite (decalageDiagonal d).
  simpl.
  rewrite equivalenceDefinitionsPrefixe.
  simpl.
  reflexivity.
  symmetry.
  apply opposeSimplificationDroiteAddition with d.
  reflexivity.
Qed.

Lemma prefixeApresListeBipartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T),
      length l1 - n = 0
      -> prefixe n (l1 ++ l2) = l1 ++ prefixe (n - length l1) l2.
Proof.
  intros n T l1 l2 H.
  distributionPrefixeConclusion.
  destruct (simplificationDroiteOpposeSoustractionNulle _ _ H) as [d eqD].
  apply eq_sym in eqD.
  rewrite <- (simplificationDroiteAddition _ _ _ eqD).
  rewrite prefixeComplet.
  simpl.
  rewrite equivalenceDefinitionsPrefixe.
  simpl.
  reflexivity.
  assumption.
Qed.


Lemma suffixeAvantListeBipartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T),
      (n - length l1 = 0)
      -> suffixe n (l1 ++ l2) = suffixe n l1 ++ l2.
Proof.
  intros n T l1 l2 H.
  distributionSuffixeConclusion.
  rewrite H.
  simpl.
  rewrite equivalenceDefinitionsSuffixe.
  simpl.
  rewrite suffixeEnZero.
  reflexivity.
Qed.

Lemma suffixeApresListeBipartiteDiff :
  forall d : nat,
  forall T, forall (l1 l2 : list T),
      suffixe (d + length l1) (l1 ++ l2) = suffixe d l2.
Proof.
  intros d T l1 l2.
  distributionSuffixeConclusion.
  rewrite suffixeVide.
  rewrite (decalageDiagonal d).
  simpl.
  rewrite equivalenceDefinitionsSuffixe.
  simpl.
  reflexivity.
  symmetry.
  apply opposeSimplificationDroiteAddition with d.
  reflexivity.
Qed.

Lemma suffixeApresListeBipartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T),
      length l1 - n = 0
      -> suffixe n (l1 ++ l2) = suffixe (n - length l1) l2.
Proof.
  intros n T l1 l2 H.
  distributionSuffixeConclusion.
  destruct (simplificationDroiteOpposeSoustractionNulle _ _ H) as [d eqD].
  apply eq_sym in eqD.
  rewrite <- (simplificationDroiteAddition _ _ _ eqD).
  rewrite suffixeVide.
  simpl.
  rewrite equivalenceDefinitionsSuffixe.
  simpl.
  reflexivity.
  assumption.
Qed.


(* Listes tripartites *)

Lemma valeurAvantListeTripartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T) (p : T),
      (S n) - length l1 = 0
      -> valeur n (l1 ++ p :: l2) = valeur n l1.
Proof.
  intros T l1 l2 p n H.
  rewrite valeurAvantListeBipartite.
  reflexivity.
  assumption.
Qed.

Lemma valeurPivotListeTripartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T) (p : T),
      n = length l1 
      -> valeur n (l1 ++ p :: l2) = [p].
Proof.
  intros T l1 l2 p n H.
  distributionValeurConclusion.
  rewrite H.
  rewrite PeanoNat.Nat.sub_diag.
  rewrite PeanoNat.Nat.sub_0_r.
  rewrite (decalageDiagonal 1).
  simpl.
  rewrite sousListeVide.
  rewrite sousListeEnZeroRF.
  rewrite prefixeEnZero.
  simpl.
  reflexivity.
  apply PeanoNat.Nat.sub_diag.
Qed.

Lemma valeurApresListeTripartite :
  forall n d : nat,
  forall T, forall (l1 l2 : list T) (p : T),
      (n - length l1 = S d)
      -> valeur n (l1 ++ p :: l2) = valeur d l2.
Proof.
  intros n d T l1 l2 p H.
  distributionValeurConclusion.
  rewrite H.
  replace (1 + n - length l1 - S d) with 1.
  simpl.
  rewrite sousListeVide.
  rewrite equivalenceDefinitionsSousListe.  
  simpl.
  reflexivity.
  apply opposeSoustractionNonNulle with d.
  assumption.
  apply simplificationDroiteAddition.
  apply simplificationDroiteAddition.
  rewrite Plus.plus_assoc_reverse.
  f_equal.
  symmetry.
  apply simplificationDroiteSoustractionNonNulle.
  assumption.
Qed.

Lemma prefixeAvantListeTripartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T) (p : T),
      n - length l1 = 0
      -> prefixe n (l1 ++ p :: l2) = prefixe n l1.
Proof.
  intros n T l1 l2 p H.
  apply prefixeAvantListeBipartite.
  assumption.
Qed.

Lemma prefixePivotListeTripartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T) (p : T),
      n = length l1 
      -> prefixe n (l1 ++ p :: l2) = l1.
Proof.
  intros n T l1 l2 p H.
  assert(n - length l1 = 0) as H'.
  {
    rewrite H.
    apply PeanoNat.Nat.sub_diag.
  }
  rewrite prefixeAvantListeBipartite.
  rewrite H.
  rewrite prefixeEnFin.
  reflexivity.
  assumption.
Qed.

Lemma prefixeApresListeTripartite :
  forall n d : nat,
  forall T, forall (l1 l2 : list T)(p : T),
      (n - length l1 = S d)
      -> prefixe n (l1 ++ p :: l2) = l1 ++ p :: prefixe d l2.
Proof.
  intros n d T l1 l2 p H.
  distributionPrefixeConclusion.
  rewrite H.
  simpl.  
  rewrite prefixeComplet.
  rewrite equivalenceDefinitionsPrefixe.
  simpl.
  reflexivity.
  apply opposeSoustractionNonNulle with d.
  assumption.
Qed.

Lemma suffixeAvantListeTripartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T)(p : T),
      (n - length l1 = 0)
      -> suffixe n (l1 ++ p :: l2) = suffixe n l1 ++ p :: l2.
Proof.
  intros n T l1 l2 p H.
  rewrite suffixeAvantListeBipartite.
  reflexivity.
  assumption.
Qed.

Lemma suffixePivotListeTripartite :
  forall n : nat,
  forall T, forall (l1 l2 : list T)(p : T),
      (n = length l1)
      -> suffixe n (l1 ++ p :: l2) = p :: l2.
Proof.
  intros n T l1 l2 p H.
  rewrite suffixeAvantListeBipartite.
  rewrite H.
  rewrite suffixeEnFin.
  reflexivity.
  rewrite H.
  apply PeanoNat.Nat.sub_diag.
Qed.

Lemma suffixeApresListeTripartite :
  forall n d : nat,
  forall T, forall (l1 l2 : list T)(p : T),
      (n - length l1 = S d)
      -> suffixe n (l1 ++ p :: l2) = suffixe d l2.
Proof.
  intros n d T l1 l2 p H.
  distributionSuffixeConclusion.
  rewrite H.
  simpl.
  rewrite suffixeVide.
  rewrite equivalenceDefinitionsSuffixe.
  simpl.
  reflexivity.
  apply opposeSoustractionNonNulle with d.
  assumption.
Qed.
