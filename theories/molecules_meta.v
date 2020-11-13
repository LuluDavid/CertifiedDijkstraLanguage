Require Export molecules.

Import ListNotations.

Proposition equivalenceDefinitionEquivalenceMoleculaire :
  forall A,
  forall LM : list (@Molecule A),
  forall M : @Molecule A,
    EquivalenceMoleculaire LM M -> EquivalenceMoleculaireP LM M.
Proof.
  intros.
  induction H; econstructor; try eassumption; reflexivity.
Qed.

Proposition equivalenceDefinitionEquivalenceMoleculaireP :
  forall A,
  forall LM : list (@Molecule A),
  forall M : @Molecule A,
    EquivalenceMoleculaireP LM M -> EquivalenceMoleculaire LM M.
Proof.
  intros.
  induction H; subst; econstructor; eassumption.
Qed.

(* Admissibilité de deux règles pratiques
 * - / permutation : dernier au lieu de premier
 * - coupure (permettant des preuves modulaires)
 *)

Lemma transpositionTripartiteMoleculaire :
  forall A : Type,
  forall LM1 LM2 LM3 : list (@Molecule A),
  forall M,
    EquivalenceMoleculaireP (LM2 ++ LM1 ++ LM3) M
    -> EquivalenceMoleculaireP (LM1 ++ LM2 ++ LM3) M.
Proof.
  intro A.
  fix HR 2.
  intros LM1 LM2 LM3 M.
  destruct LM2 as [ | tLM2 rLM2].
  {
    simpl.
    tauto.
  }
  {
    intro Equiv.
    replace (LM1 ++ (tLM2 :: rLM2) ++ LM3) with ((LM1 ++ [tLM2]) ++ rLM2 ++ LM3).
    apply HR.
    replace (rLM2 ++ (LM1 ++ [tLM2]) ++ LM3)
      with ((rLM2 ++ LM1) ++ [tLM2] ++ LM3).
    eapply (premierGaucheP _ _ (length (rLM2 ++ LM1)) tLM2).
    simpl.
    apply valeurListeConsApresListe.
    rewrite prefixeGaucheConcatenation.
    replace (suffixe (S (length (rLM2 ++ LM1))) ((rLM2 ++ LM1) ++ [tLM2] ++ LM3))
      with (suffixe (length ((rLM2 ++ LM1) ++ [tLM2]))
                    (((rLM2 ++ LM1) ++ [tLM2]) ++ LM3)).
    rewrite suffixeDroiteConcatenation.
    replace (tLM2 :: (rLM2 ++ LM1) ++ LM3) with ((tLM2 :: rLM2) ++ LM1 ++ LM3).
    assumption.
    egaliteListes.
    f_equal.
    apply longueurListeSingleton.
    egaliteListes.
    egaliteListes.
    egaliteListes.
  }
Qed.

Proposition dernierGaucheP :
  forall A : Type,
  forall LM : list (@Molecule A),
  forall M : (@Molecule A),
  forall n LMn,
    valeur n LM = [LMn] ->
    EquivalenceMoleculaireP (((prefixe n LM) ++ (suffixe (S n) LM)) ++ [LMn]) M ->
    EquivalenceMoleculaireP LM M.
Proof.
  intro A.
  intros LM M n LMn eqLMn  Equiv.
  rewrite <- (@decompositionListeAvecPivot _ n LM).
  replace (prefixe n LM ++ valeur n LM ++ suffixe (S n) LM)
    with ((prefixe n LM ++ valeur n LM) ++ suffixe (S n) LM ++ []).
  apply transpositionTripartiteMoleculaire.
  replace (suffixe (S n) LM ++ (prefixe n LM ++ valeur n LM) ++ [])
    with (suffixe (S n) LM ++ prefixe n LM ++ valeur n LM).
  apply transpositionTripartiteMoleculaire.
  rewrite eqLMn.
  replace (prefixe n LM ++ suffixe (S n) LM ++ [LMn])
    with ((prefixe n LM ++ suffixe (S n) LM) ++ [LMn]).
  assumption.
  egaliteListes.
  egaliteListes.
  egaliteListes.
Qed.

Proposition dernierGauche :
  forall {A : Type},
  forall LM : list (@Molecule A),
  forall M : (@Molecule A),
  forall n LMn,
    valeur n LM = [LMn] ->
    EquivalenceMoleculaire (((prefixe n LM) ++ (suffixe (S n) LM)) ++ [LMn]) M ->
    EquivalenceMoleculaire LM M.
Proof.
  intros A LM M n LMn eqN Equiv.
  apply equivalenceDefinitionEquivalenceMoleculaireP.
  apply equivalenceDefinitionEquivalenceMoleculaire in Equiv.
  apply dernierGaucheP with n LMn.
  assumption.
  assumption.
Qed.

Arguments dernierGauche {_ _ _}.

Lemma inversionUnGauche :
  forall A : Type, 
      forall LM1 LM2 (M : @Molecule A),
        EquivalenceMoleculaireP  (LM1 ++ un :: LM2) M
        -> EquivalenceMoleculaireP (LM1 ++ LM2) M.
Proof.
  intro A.
  fix HR 4.
  intros LM1 LM2 M Equiv.
  destruct Equiv as [ b eqG eqD | eqG eqD
                      | LM' eqG equivPrem | g M1 M2 eqM equivPrem1 equivPrem2
                      | LM' M1 M2 eqG equivPrem
                      | n LMn eqLMn equivPremier ] eqn:cas.
  { (* cas identité atome *)
    destruct (simplificationSingleton _ _ _ _ _ eqG) as [eqB [eq1 eq2]].
    discriminate eqB.
  }
  { (*cas neutre droite *)
    destruct LM1.
    discriminate eqG.
    discriminate eqG.
  }
  { (* cas neutre gauche *)
    destruct LM1 as [ | tLM1 rLM1].
    {
      simpl in eqG.
      injection eqG.
      intro eq2.
      simpl.
      rewrite eq2.
      assumption.
    }
    {
      simpl in eqG.
      injection eqG.
      intros eqRLM1  eqTLM1.
      rewrite eqTLM1.
      simpl.
      replace (un :: rLM1 ++ LM2) with ([un] ++ rLM1 ++ LM2).
      apply transpositionTripartiteMoleculaire.
      simpl.
      rewrite eqRLM1.
      assumption.
      egaliteListes.
    }
  }    
  { (* cas conjonction multiplicative droite *)
    assert (EquivalenceMoleculaireP (prefixe g (LM1 ++ un :: LM2)) M1) as equivPrem1'.
    {
      assumption.
    }
    assert (EquivalenceMoleculaireP (suffixe g (LM1 ++ un :: LM2)) M2) as equivPrem2'.
    {
      assumption.
    }
    destruct (g - length LM1) as [ | pgMlLM1] eqn:cas_gMlLM1.
    { (* un dans la prémisse droite *)
      rewrite (prefixeAvantListeBipartite g) in equivPrem1'; try assumption.
      rewrite (suffixeAvantListeBipartite g) in equivPrem2'; try assumption.
      eapply (conjonctionMultiplicativeDroiteP _ _ g).
      rewrite eqM.
      reflexivity.
      rewrite (prefixeAvantListeBipartite g); try assumption.
      rewrite (suffixeAvantListeBipartite g); try assumption.
      apply HR.
      assumption.
    }
    { (* un dans la prémisse gauche *)
      rewrite (prefixeApresListeTripartite g pgMlLM1) in equivPrem1';
        try assumption.
      rewrite (suffixeApresListeTripartite g pgMlLM1) in equivPrem2';
        try assumption.
      eapply (conjonctionMultiplicativeDroiteP _ _ (pgMlLM1 + length LM1)).
      rewrite eqM.
      reflexivity.
      rewrite (prefixeApresListeBipartiteDiff pgMlLM1).
      apply HR.
      assumption.
      rewrite (suffixeApresListeBipartiteDiff pgMlLM1).
      assumption.
    }
  } 
  { (* conjonction multiplicative gauche *)
    destruct LM1 as [ | tLM1 rLM1].
    {
      simpl in eqG.
      injection eqG.
      intros _ Absurde.
      discriminate Absurde.
    }
    {
      simpl in eqG.
      injection eqG.
      intros eqLM' eqtLM1.
      simpl.
      eapply conjonctionMultiplicativeGaucheP.
      rewrite eqtLM1.
      reflexivity.
      replace (M1 :: M2 :: rLM1 ++ LM2) with
          ((M1 :: M2 :: rLM1) ++ LM2).
      apply HR.
      simpl.
      rewrite eqLM'.
      assumption.
      egaliteListes.
    }
  }
  { (* premier Gauche *)
    assert (
        EquivalenceMoleculaireP
          (LMn :: prefixe n (LM1 ++ un :: LM2) ++ suffixe (S n) (LM1 ++ un :: LM2))
          M
      ) as equivPremier'.
    {
      assumption.
    }
    assert(
        valeur n (LM1 ++ un :: LM2) = [LMn]
      ) as eqLMn'.
    {
      assumption.
    }
    destruct (n - length LM1) as [ | pnMlLM1] eqn:cas_nMlLM1.
    {
      destruct(S n - length LM1) as [ | pSnMlLM1] eqn: cas_SnMlLM1.
      {
        rewrite (valeurAvantListeTripartite n) in eqLMn'; try assumption.
        rewrite (prefixeAvantListeTripartite n) in equivPremier'; try assumption.
        rewrite (suffixeAvantListeTripartite (S n)) in equivPremier'; try assumption.
        eapply premierGaucheP with n LMn.
        rewrite (valeurAvantListeBipartite n); try assumption.
        rewrite (prefixeAvantListeBipartite n); try assumption.
        rewrite (suffixeAvantListeBipartite (S n)); try assumption.
        replace
          (LMn :: prefixe n LM1 ++ suffixe (S n) LM1 ++ LM2)
          with
            ((LMn :: prefixe n LM1 ++ suffixe (S n) LM1) ++ LM2).
        apply HR.
        simpl.
        replace
          (LMn :: (prefixe n LM1 ++ suffixe (S n) LM1) ++ un :: LM2)
          with
            (LMn :: prefixe n LM1 ++ suffixe (S n) LM1 ++ un :: LM2).
        assumption.
        egaliteListes.
        egaliteListes.
      }
      {
        destruct (casEgaliteSoustractionNulle _ _ _ cas_nMlLM1 cas_SnMlLM1) as [eqN eqpSn].
        rewrite (valeurPivotListeTripartite n) in eqLMn'; try assumption.
        rewrite (prefixePivotListeTripartite n) in equivPremier'; try assumption.
        rewrite (suffixeApresListeTripartite (S n) 0) in equivPremier'; try assumption.
        rewrite suffixeEnZero in equivPremier'; try assumption.
        replace (LM1 ++ LM2) with ([] ++ (LM1 ++ LM2)).
        apply HR.
        simpl.
        injection eqLMn'.
        intro eqPivot.
        rewrite eqPivot.
        assumption.
        egaliteListes.
        rewrite <- eqpSn.
        assumption.
      }
    }      
    {
      rewrite (valeurApresListeTripartite n pnMlLM1) in eqLMn'; try assumption.
      rewrite (prefixeApresListeTripartite n pnMlLM1) in equivPremier'; try assumption.
      rewrite (suffixeApresListeTripartite (S n) (S pnMlLM1)) in equivPremier'; try assumption.
      eapply premierGaucheP with (pnMlLM1 + length LM1) LMn.
      rewrite (valeurApresListeBipartiteDiff pnMlLM1).      
      assumption.
      rewrite (prefixeApresListeBipartiteDiff pnMlLM1).
      replace (S (pnMlLM1 + length LM1)) with (S pnMlLM1 + length LM1).
      rewrite (suffixeApresListeBipartiteDiff (S pnMlLM1)).
      replace (LMn :: (LM1 ++ prefixe pnMlLM1 LM2) ++ suffixe (S pnMlLM1) LM2)
        with ((LMn :: LM1) ++ (prefixe pnMlLM1 LM2) ++ suffixe (S pnMlLM1) LM2).
      apply HR.
      simpl.
      replace (LMn :: LM1 ++ un :: prefixe pnMlLM1 LM2 ++ suffixe (S pnMlLM1) LM2)
        with (LMn :: (LM1 ++ un :: prefixe pnMlLM1 LM2) ++ suffixe (S pnMlLM1) LM2).
      assumption.
      egaliteListes.
      egaliteListes.
      reflexivity.
      apply successeurSoustractionNonNulle; assumption.
    }
  }
Qed.

Lemma inversionConjonctionMultiplicativeGauche :
  forall A : Type, forall M1 M2 : (@Molecule A),
      forall LM1 LM2 N,
        EquivalenceMoleculaireP  (LM1 ++ (M1 ⊗ M2) :: LM2) N
        -> EquivalenceMoleculaireP (LM1 ++ M1 :: M2 :: LM2) N.
Proof.
  intro A.
  fix HR 6.
  intros M1 M2 LM1 LM2 N Equiv.
  destruct Equiv as [ b eqG eqD | eqG eqD
                      | LM' eqG equivPrem | g M1' M2' eqM equivPrem1 equivPrem2
                      | LM' M1' M2' eqG equivPrem
                      | n LMn eqLMn equivPremier ] eqn:cas.
  { (* cas identité atome *)
    destruct LM1 as [ | tLM1 rLM1].
    discriminate eqG.
    simpl.
    injection eqG.
    intros Absurde _.
    destruct rLM1.
    discriminate Absurde.
    discriminate Absurde.
  }
  { (*cas neutre droite *)
    destruct LM1.
    discriminate eqG.
    discriminate eqG.
  }
  { (* cas neutre gauche *)
    destruct LM1 as [ | tLM1 rLM1].
    {
      discriminate eqG.
    }
    {
      injection eqG.
      intros eqRLM1  eqTLM1.
      rewrite eqTLM1.
      eapply unGaucheP.
      simpl.
      reflexivity.
      apply HR.
      rewrite eqRLM1.
      assumption.
    }
  }    
  { (* cas conjonction multiplicative droite *)
    assert (EquivalenceMoleculaireP (prefixe g (LM1 ++ M1 ⊗ M2 :: LM2)) M1') as equivPrem1'.
    {
      assumption.
    }
    assert (EquivalenceMoleculaireP (suffixe g (LM1 ++ M1 ⊗ M2 :: LM2)) M2') as equivPrem2'.
    {
      assumption.
    }
    destruct (g - length LM1) as [ | pgMlLM1] eqn:cas_gMlLM1.
    { (* M1 ⊗ M2 dans la prémisse droite *)
      rewrite (prefixeAvantListeBipartite g) in equivPrem1'; try assumption.
      rewrite (suffixeAvantListeBipartite g) in equivPrem2'; try assumption.
      eapply (conjonctionMultiplicativeDroiteP _ _ g).
      rewrite eqM.
      reflexivity.
      rewrite (prefixeAvantListeBipartite g); try assumption.
      rewrite (suffixeAvantListeBipartite g); try assumption.
      apply HR.
      assumption.
    }
    { (* M1 ⊗ M2 dans la prémisse gauche *)
      rewrite (prefixeApresListeTripartite g pgMlLM1) in equivPrem1';
        try assumption.
      rewrite (suffixeApresListeTripartite g pgMlLM1) in equivPrem2';
        try assumption.
      eapply (conjonctionMultiplicativeDroiteP _ _ (S (S pgMlLM1) + length LM1) ).
      rewrite eqM.
      reflexivity.
      rewrite (prefixeApresListeBipartiteDiff (S (S pgMlLM1))); try assumption.
      simpl.
      apply HR.
      assumption.
      rewrite (suffixeApresListeBipartiteDiff (S (S pgMlLM1))); try assumption.
    } 
  }
  { (* conjonction multiplicative gauche *)
    destruct LM1 as [ | tLM1 rLM1].
    {
      simpl.
      injection eqG.
      intros eqLM2 eqM2 eqM1.
      rewrite eqLM2.
      rewrite eqM2.
      rewrite eqM1.
      assumption.
    }
    {
      injection eqG.
      intros eqLM' eqtLM1.
      simpl.
      eapply conjonctionMultiplicativeGaucheP.
      rewrite eqtLM1.
      reflexivity.
      replace (M1' :: M2' :: rLM1 ++ M1 :: M2 :: LM2) with
          ((M1' :: M2' :: rLM1) ++ M1 :: M2 :: LM2).
      apply HR.
      simpl.
      rewrite eqLM'.
      assumption.
      egaliteListes.
    }
  }
  { (* premier Gauche *)
    assert (
        EquivalenceMoleculaireP
          (LMn :: prefixe n (LM1 ++ M1 ⊗ M2 :: LM2) ++ suffixe (S n) (LM1 ++ M1 ⊗ M2 :: LM2))
          N
      ) as equivPremier'.
    {
      assumption.
    }
    assert(
        valeur n (LM1 ++ M1 ⊗ M2 :: LM2) = [LMn]
      ) as eqLMn'.
    {
      assumption.
    }
    destruct (n - length LM1) as [ | pnMlLM1] eqn:cas_nMlLM1.
    {
      destruct(S n - length LM1) as [ | pSnMlLM1] eqn: cas_SnMlLM1.
      {
        rewrite (valeurAvantListeTripartite n) in eqLMn'; try assumption.
        rewrite (prefixeAvantListeTripartite n) in equivPremier'; try assumption.
        rewrite (suffixeAvantListeTripartite (S n)) in equivPremier'; try assumption.
        eapply premierGaucheP with n LMn.
        rewrite (valeurAvantListeTripartite n); try assumption.
        rewrite (prefixeAvantListeTripartite n); try assumption.
        rewrite (suffixeAvantListeTripartite (S n)); try assumption.
        replace
          (LMn :: prefixe n LM1 ++ suffixe (S n) LM1 ++ M1 :: M2 :: LM2)
          with
            ((LMn :: prefixe n LM1 ++ suffixe (S n) LM1) ++ M1 :: M2 :: LM2).
        apply HR.
        simpl.
        replace
          (LMn :: (prefixe n LM1 ++ suffixe (S n) LM1) ++ M1 ⊗ M2 :: LM2)
          with
            (LMn :: prefixe n LM1 ++ suffixe (S n) LM1 ++ M1 ⊗ M2 :: LM2).
        assumption.
        egaliteListes.
        egaliteListes.
      }
      {
        assert((n = length LM1) /\ (pSnMlLM1 = 0)) as [eqNlLM1 eqpSnMlLM1].
        {
          apply casEgaliteSoustractionNulle; assumption.
        }
        rewrite (valeurPivotListeTripartite n) in eqLMn'; try assumption.
        rewrite (prefixePivotListeTripartite n) in equivPremier'; try assumption.
        rewrite (suffixeApresListeTripartite (S n) 0) in equivPremier'; try assumption.
        rewrite suffixeEnZero in equivPremier'; try assumption.
        eapply premierGaucheP with (length (LM1 ++ [M1])) M2.
        replace (LM1 ++ M1 :: M2 :: LM2) with ((LM1 ++ [M1]) ++ M2 :: LM2). 
        apply valeurListeConsApresListe.
        egaliteListes.
        replace  (prefixe (length (LM1 ++ [M1])) (LM1 ++ M1 :: M2 :: LM2))
          with (prefixe (length (LM1 ++ [M1])) ((LM1 ++ [M1]) ++ (M2 :: LM2))).
        rewrite prefixeGaucheConcatenation.
        replace (suffixe (S (length (LM1 ++ [M1]))) (LM1 ++ M1 :: M2 :: LM2))
          with (suffixe (length ((LM1 ++ [M1]) ++ [M2]))
                        (((LM1 ++ [M1]) ++ [M2]) ++ LM2)).
        rewrite suffixeDroiteConcatenation.
        eapply premierGaucheP with (length (M2 :: LM1)) M1.
        replace (M2 :: (LM1 ++ [M1]) ++ LM2) with ((M2 :: LM1) ++ M1 :: LM2).
        rewrite valeurListeConsApresListe.
        reflexivity.
        egaliteListes.
        replace  (prefixe (length (M2 :: LM1)) (M2 :: (LM1 ++ [M1]) ++ LM2))
          with (prefixe (length (M2 :: LM1)) ((M2 :: LM1) ++ [M1] ++ LM2)).
        rewrite prefixeGaucheConcatenation.
        replace (suffixe (S (length (M2 :: LM1))) (M2 :: (LM1 ++ [M1]) ++ LM2))
          with (suffixe (length ((M2 :: LM1) ++ [M1])) (((M2 :: LM1) ++ [M1]) ++ LM2)).
        rewrite suffixeDroiteConcatenation.
        replace (M1 :: (M2 :: LM1) ++ LM2) with ([] ++ M1 :: M2 :: LM1 ++ LM2).
        apply HR.
        simpl.
        injection eqLMn'; intro eqPivot.
        rewrite eqPivot.
        assumption.
        egaliteListes.
        f_equal.        
        apply longueurListeSingleton.
        f_equal.        
        egaliteListes.
        f_equal.
        apply longueurListeSingleton.
        egaliteListes.
        f_equal.
        egaliteListes.
        rewrite <- eqpSnMlLM1.
        assumption.
      }
    }      
    {
      rewrite (valeurApresListeTripartite n pnMlLM1) in eqLMn'; try assumption.
      rewrite (prefixeApresListeTripartite n pnMlLM1) in equivPremier'; try assumption.
      rewrite (suffixeApresListeTripartite (S n) (S pnMlLM1)) in equivPremier'; try assumption.
      replace(LM1 ++  M1 :: M2 :: LM2) with ((LM1 ++ [M1] ++ [M2]) ++ LM2).
      eapply premierGaucheP with (pnMlLM1 + (length (LM1 ++ [M1 ; M2]))) LMn.
      rewrite (valeurApresListeBipartiteDiff pnMlLM1); try assumption.
      rewrite (prefixeApresListeBipartiteDiff pnMlLM1); try assumption.
      replace (S (pnMlLM1 + length (LM1 ++ [M1; M2])))
        with (S pnMlLM1 + length (LM1 ++ [M1; M2])).
      rewrite (suffixeApresListeBipartiteDiff (S pnMlLM1)); try assumption.
      simpl.
      replace
        (LMn :: ((LM1 ++ [M1; M2]) ++ prefixe pnMlLM1 LM2) ++ suffixe (S pnMlLM1) LM2)
        with
        (LMn :: LM1 ++ M1 :: M2 :: prefixe pnMlLM1 LM2 ++ suffixe (S pnMlLM1) LM2).  
      apply (HR M1 M2 (LMn :: LM1) (prefixe pnMlLM1 LM2 ++ suffixe (S pnMlLM1) LM2) N).
      replace 
        ((LMn :: LM1) ++ M1 ⊗ M2 :: prefixe pnMlLM1 LM2 ++ suffixe (S pnMlLM1) LM2)
        with
          (LMn :: (LM1 ++ M1 ⊗ M2 :: prefixe pnMlLM1 LM2) ++ suffixe (S pnMlLM1) LM2).     
      assumption.
      egaliteListes.
      egaliteListes.
      reflexivity.
      egaliteListes.
      apply successeurSoustractionNonNulle.
      assumption.
    }
  }
Qed.

Corollary inversionC :
  forall A : Type, forall M1 M2 : (@Molecule A),
      forall LM N,
        EquivalenceMoleculaire  ((M1 ⊗ M2) :: LM) N
        -> EquivalenceMoleculaire (M1 :: M2 :: LM) N.
Proof.
  intros. rewrite <- (app_nil_l (M1 :: M2 :: LM)).
  apply equivalenceDefinitionEquivalenceMoleculaireP.
  apply (inversionConjonctionMultiplicativeGauche _ _ _ [] LM); simpl.
  apply equivalenceDefinitionEquivalenceMoleculaire; trivial.
Qed.

Proposition coupureMoleculeEtendueP :
  forall {A : Type},
  forall LM1 LM2 LM3 : list (@Molecule A),
  forall M N : (@Molecule A),
    EquivalenceMoleculaireP LM1 N
    -> EquivalenceMoleculaireP (LM2 ++ N :: LM3) M
    -> EquivalenceMoleculaireP (LM1 ++ LM2 ++ LM3) M.
Proof.
  intro A.
  fix HR 6.
  intros LM1 LM2 LM3 M N EquivG EquivD.
  destruct EquivG as [ b eqG eqD | eqG eqD
                      | LM eqG equivPrem | g M1 M2 eqM equivPrem1 equivPrem2
                      | LM M1 M2 eqG equivPrem
                      | n LMn eqLMn equivPremier ] eqn:casD.
  { (* identité atome *)
    apply transpositionTripartiteMoleculaire.
    rewrite eqG.
    rewrite <- eqD.
    simpl.
    assumption.
  }
  { (* unité à droite *)
    rewrite eqG.
    simpl.
    apply inversionUnGauche.
    rewrite <- eqD.
    assumption.
  }
  { (* unité à gauche *)
    eapply unGaucheP.
    rewrite eqG.
    simpl.
    reflexivity.
    apply HR with N.
    assumption.
    assumption.
  }
  { (* conjonction multiplicative droite *)
    rewrite eqM in EquivD.
    apply inversionConjonctionMultiplicativeGauche in EquivD.
    rewrite <- (decompositionListe _ g LM1).
    replace ((prefixe g LM1 ++ suffixe g LM1) ++ LM2 ++ LM3)
      with (prefixe g LM1 ++ suffixe g LM1 ++ LM2 ++ LM3).
    apply transpositionTripartiteMoleculaire.
    replace (suffixe g LM1 ++ prefixe g LM1 ++ LM2 ++ LM3)
      with (suffixe g LM1 ++ (prefixe g LM1 ++ LM2) ++ LM3).
    apply HR with M2.
    assumption.
    replace ((prefixe g LM1 ++ LM2) ++ M2 :: LM3)
      with (prefixe g LM1 ++ LM2 ++ M2 :: LM3).
    apply HR with M1.
    assumption.
    assumption.
    egaliteListes.
    egaliteListes.
    egaliteListes.
  }
  { (* conjonction multiplicative gauche *)
    eapply conjonctionMultiplicativeGaucheP.
    rewrite eqG.
    simpl.
    reflexivity.
    replace (M1 :: M2 :: LM ++ LM2 ++ LM3) with
        ((M1 :: M2 :: LM) ++ LM2 ++ LM3).
    apply HR with N.
    assumption.
    assumption.
    egaliteListes.
  }
  { (* premier gauche *)
    destruct (S n - length LM1) as [ | dSn] eqn:eqDSn.
    {
      assert(n - length LM1 =  0) as eqDn.
      {
        apply predecesseurSoustractionNulle.
        assumption.
      }
      eapply (premierGaucheP _ _ n LMn).
      rewrite (valeurAvantListeBipartite n); try assumption.
      rewrite (prefixeAvantListeBipartite n); try assumption.
      rewrite (suffixeAvantListeBipartite (S n)); try assumption.
      replace (LMn :: prefixe n LM1 ++ suffixe (S n) LM1 ++ LM2 ++ LM3)
        with ((LMn :: prefixe n LM1 ++ suffixe (S n) LM1) ++ LM2 ++ LM3).
      apply HR with N.
      assumption.
      assumption.
      egaliteListes.      
    }
    {
      assert(valeur n LM1 = [LMn]) as Absurde.
      {
        assumption.
      }  
      unfold valeur in Absurde.
      rewrite sousListeVide in Absurde.
      discriminate Absurde.
      symmetry.
      apply opposeSimplificationDroiteAddition with dSn.
      apply simplificationDroiteSoustractionNonNulle in eqDSn.
      simpl in eqDSn.
      injection eqDSn.
      intro Ccl.
      symmetry; assumption.
    }
  }
Qed.    

Proposition coupureMoleculeP :
  forall {A : Type},
  forall LM : list (@Molecule A),
  forall M : (@Molecule A),
  forall g, forall N,
      EquivalenceMoleculaireP (prefixe g LM) N ->
      EquivalenceMoleculaireP (N :: (suffixe g LM)) M ->
      EquivalenceMoleculaireP LM M.
Proof.
  intros A LM M g N PremG PremD.
  replace LM with ((prefixe g LM) ++ [] ++ (suffixe g LM)).
  apply coupureMoleculeEtendueP with N.
  assumption.
  assumption.
  simpl.
  apply decompositionListe.
Qed.

Proposition coupureMolecule :
  forall {A : Type},
  forall {LM : list (@Molecule A)},
  forall {M : (@Molecule A)},
  forall g, forall N,
      EquivalenceMoleculaire (prefixe g LM) N ->
      EquivalenceMoleculaire (N :: (suffixe g LM)) M ->
      EquivalenceMoleculaire LM M.
Proof.
  intros A LM M g N EquivG EquivD.
  apply equivalenceDefinitionEquivalenceMoleculaireP.
  apply equivalenceDefinitionEquivalenceMoleculaire in EquivD.
  apply equivalenceDefinitionEquivalenceMoleculaire in EquivG.
  apply coupureMoleculeP with g N.
  assumption.
  assumption.
Qed.

Proposition dernierDroite :
  forall {A : Type},
  forall LM : list (@Molecule A),
  forall M : (@Molecule A),
  forall n LMn,
    valeur n LM = [LMn] ->
    EquivalenceMoleculaire (((prefixe n LM) ++ (suffixe (S n) LM)) ++ [LMn]) M ->
    EquivalenceMoleculaire LM M.
Proof.
  intros A LM M n LMn eqLMn Equiv.
  apply equivalenceDefinitionEquivalenceMoleculaireP.
  apply equivalenceDefinitionEquivalenceMoleculaire in Equiv.
  apply dernierGaucheP with n LMn.
  assumption.
  assumption.
Qed.


(* Propriétés de l'équivalence moléculaire *)

(*
- congruence
- réflexivité
- symétrie : voir à la fin, car plus compliqué
- transitivité
*)

Lemma congruenceMoleculaire :
  forall A,
  forall M1 M2 N1 N2 : @Molecule A,
    EquivalenceMoleculaire [M1] M2
    -> EquivalenceMoleculaire [N1] N2
    -> EquivalenceMoleculaire [M1 ⊗ N1] (M2 ⊗ N2).
Proof.
  intro A.
  intros M1 M2 N1 N2 eqM eqN.
  apply (conjonctionMultiplicativeGauche).
  eapply (conjonctionMultiplicativeDroite 1).
  simpl.
  assumption.
  simpl.
  assumption.
Qed.

Lemma reflexiviteMoleculaire :
  forall A : Type, forall M : (@Molecule A),
      EquivalenceMoleculaire [M] M.
Proof.
  intro A.
  fix HR 1.
  intro M.
  destruct M as [ | a | M1 M2 ].
  {
    apply unGauche.
    apply unDroite.
  }
  {
    apply identiteAtome.
  }
  {
    apply conjonctionMultiplicativeGauche.
    apply (conjonctionMultiplicativeDroite 1).
    apply HR.
    apply HR.
  }
Qed.

Lemma transitiviteMoleculaire :
  forall A : Type, forall M1 M2 M3 : (@Molecule A),
      EquivalenceMoleculaire [M1] M2
      -> EquivalenceMoleculaire [M2] M3
      -> EquivalenceMoleculaire [M1] M3.
Proof.
  intros.
  apply coupureMolecule with 1 M2; assumption.
Qed.

Lemma associativiteDroiteMoleculaire :
  forall A : Type, forall M1 M2 M3: (@Molecule A),
      EquivalenceMoleculaire [M1 ⊗ (M2 ⊗ M3)] ((M1 ⊗ M2) ⊗ M3). 
Proof.
  intros A M1 M2 M3.
  apply conjonctionMultiplicativeGauche.
  eapply (premierGauche 1).
  reflexivity.
  simpl.
  apply conjonctionMultiplicativeGauche.
  eapply (premierGauche 2).
  reflexivity.
  simpl.
  apply (conjonctionMultiplicativeDroite 2).
  simpl.
  apply (conjonctionMultiplicativeDroite 1).
  simpl.
  apply reflexiviteMoleculaire.
  simpl.
  apply reflexiviteMoleculaire.
  simpl.
  apply reflexiviteMoleculaire.
Qed.

Lemma associativiteGaucheMoleculaire :
  forall A : Type, forall M1 M2 M3: (@Molecule A),
        EquivalenceMoleculaire [(M1 ⊗ M2) ⊗ M3] (M1 ⊗ (M2 ⊗ M3)). 
Proof.
  intros A M1 M2 M3.
  apply conjonctionMultiplicativeGauche.
  apply conjonctionMultiplicativeGauche.
  apply (conjonctionMultiplicativeDroite 1).
  simpl.
  apply reflexiviteMoleculaire.
  simpl.
  apply (conjonctionMultiplicativeDroite 1).
  simpl.
  apply reflexiviteMoleculaire.
  simpl.
  apply reflexiviteMoleculaire.
Qed.

Lemma commutativiteMoleculaire :
  forall A : Type, forall M N: (@Molecule A),
        EquivalenceMoleculaire [M ⊗ N] (N ⊗ M). 
Proof.
  intros A M N.
  apply conjonctionMultiplicativeGauche.
  eapply (premierGauche 1).
  reflexivity.
  simpl.
  apply (conjonctionMultiplicativeDroite 1).
  simpl.
  apply reflexiviteMoleculaire.
  simpl.
  apply reflexiviteMoleculaire.
Qed.

Lemma neutraliteGaucheMoleculaire :
forall A : Type, forall M : (@Molecule A),
        EquivalenceMoleculaire [un ⊗ M] M. 
Proof.
  intros A M.
  apply conjonctionMultiplicativeGauche.
  apply unGauche.
  apply reflexiviteMoleculaire.
Qed.

Lemma neutraliteDroiteMoleculaire :
forall A : Type, forall M : (@Molecule A),
        EquivalenceMoleculaire [M ⊗ un] M. 
Proof.
  intros A M.
  apply conjonctionMultiplicativeGauche.
  eapply (premierGauche 1).
  reflexivity.
  apply unGauche.
  apply reflexiviteMoleculaire.
Qed.

Proposition reductionHomomorpheListeMoleculesEnConjonctionMultiplicativeDroite :
  forall A : Type,
  forall l l1 l2 : list (@Molecule A),
    l = l1 ++ l2
    -> EquivalenceMoleculaire 
         [reductionListeMoleculesEnConjonctionMultiplicative l]
         ((reductionListeMoleculesEnConjonctionMultiplicative l1)
            ⊗ (reductionListeMoleculesEnConjonctionMultiplicative l2)).
Proof.
  intro A.
  fix HR 2.
  intros l l1 l2 eqL.
  destruct l1 as [ | t1 r1].
  {
    simpl in eqL.
    simpl.
    rewrite eqL.
    apply (conjonctionMultiplicativeDroite 0).
    apply unDroite.
    simpl.
    apply reflexiviteMoleculaire.    
  }
  {
    rewrite eqL.
    simpl.
    eapply (coupureMolecule 1).
    simpl.
    apply conjonctionMultiplicativeGauche.
    apply (conjonctionMultiplicativeDroite 1).
    simpl.
    apply reflexiviteMoleculaire.
    simpl.
    apply (HR _ r1 l2).
    reflexivity.
    simpl.
    apply associativiteDroiteMoleculaire.    
  }
Qed.

Proposition reductionHomomorpheListeMoleculesEnConjonctionMultiplicativeGauche :
  forall A : Type,
  forall l l1 l2 : list (@Molecule A),
    l = l1 ++ l2
    -> EquivalenceMoleculaire 
         [(reductionListeMoleculesEnConjonctionMultiplicative l1)
            ⊗ (reductionListeMoleculesEnConjonctionMultiplicative l2)]
         (reductionListeMoleculesEnConjonctionMultiplicative l).
Proof.
  intro A.
  fix HR 2.
  intros l l1 l2 eqL.
  destruct l1 as [ | t1 r1].
  {
    simpl in eqL.
    simpl.
    rewrite eqL.
    apply conjonctionMultiplicativeGauche.
    apply unGauche.
    apply reflexiviteMoleculaire.    
  }
  {
    rewrite eqL.
    simpl.
    apply conjonctionMultiplicativeGauche.
    apply conjonctionMultiplicativeGauche.
    apply (conjonctionMultiplicativeDroite 1).
    simpl.
    apply reflexiviteMoleculaire.
    simpl.
    eapply (coupureMolecule 2).
    simpl.
    eapply (conjonctionMultiplicativeDroite 1).
    simpl.
    apply reflexiviteMoleculaire.
    apply reflexiviteMoleculaire.
    simpl.
    apply (HR _ r1 l2).
    reflexivity.
  }
Qed.

Lemma symmetrieMoleculaireP :
  forall A,
  forall LM : list (@Molecule A),
  forall M : @Molecule A,
    EquivalenceMoleculaireP LM M
    -> EquivalenceMoleculaireP [M] (reductionListeMoleculesEnConjonctionMultiplicative LM).
Proof.
  intros A.
  fix HR 3.
  intros LM M EqM.
  destruct EqM as [ b eqG eqD | eqG eqD
                      | LM' eqG equivPrem | g M1 M2 eqM equivPrem1 equivPrem2
                      | LM' M1 M2 eqG equivPrem
                      | n LMn eqLMn equivPremier ] eqn:cas.
  { (* identite atome *)
    rewrite eqG.
    rewrite eqD.
    simpl.
    eapply (conjonctionMultiplicativeDroiteP _ _ 1).
    reflexivity.
    simpl.
    eapply identiteAtomeP.
    reflexivity.
    reflexivity.
    simpl.
    apply unDroiteP.
    reflexivity.
    reflexivity.
  }
  { (* unité droite *)
    rewrite eqG.
    rewrite eqD.
    simpl.
    apply equivalenceDefinitionEquivalenceMoleculaire.
    apply reflexiviteMoleculaire.
  }
  { (* unité gauche *)
    rewrite eqG.
    simpl.
    eapply (conjonctionMultiplicativeDroiteP _ _ 0).
    reflexivity.
    simpl.
    apply unDroiteP.
    reflexivity.
    reflexivity.
    simpl.
    apply (HR LM' M).
    assumption.
  }
  { (* conjonction multiplicative droite *)
    rewrite eqM.
    eapply conjonctionMultiplicativeGaucheP.
    reflexivity.
    eapply (coupureMoleculeP _ _ 2).
    simpl.
    eapply (conjonctionMultiplicativeDroiteP _ _ 1).
    reflexivity.
    simpl.
    apply (HR (prefixe g LM) M1).
    assumption.
    simpl.
    apply (HR (suffixe g LM) M2).
    assumption.
    simpl.
    apply equivalenceDefinitionEquivalenceMoleculaire.
    apply reductionHomomorpheListeMoleculesEnConjonctionMultiplicativeGauche.
    symmetry.
    apply decompositionListe.
  }
  { (* conjonction multiplicative gauche *)
    rewrite eqG.
    eapply (coupureMoleculeP _ _ 1).
    simpl.
    apply (HR (M1 :: M2 :: LM') M).
    assumption.
    simpl.
    apply equivalenceDefinitionEquivalenceMoleculaire.
    apply associativiteDroiteMoleculaire.
  }
  { (* premier gauche *)    
    set (prefLM := (prefixe n LM)) in *.
    set (suffLM := (suffixe (S n) LM)) in *.            
    eapply (coupureMoleculeP _ _ 1).
    simpl.
    apply (HR (LMn :: prefLM ++ suffLM) M).
    assumption.
    simpl.
    eapply conjonctionMultiplicativeGaucheP.
    reflexivity.
    eapply (coupureMoleculeP
              _ _ 2
              ((reductionListeMoleculesEnConjonctionMultiplicative [LMn])
                 ⊗ ((reductionListeMoleculesEnConjonctionMultiplicative prefLM)
                      ⊗ (reductionListeMoleculesEnConjonctionMultiplicative suffLM)))).
    simpl.
    eapply (conjonctionMultiplicativeDroiteP _ _ 1).
    reflexivity.
    simpl.
    eapply (conjonctionMultiplicativeDroiteP _ _ 1).
    reflexivity.
    apply equivalenceDefinitionEquivalenceMoleculaire.
    apply reflexiviteMoleculaire.
    apply unDroiteP; reflexivity.
    simpl.
    apply equivalenceDefinitionEquivalenceMoleculaire.
    apply reductionHomomorpheListeMoleculesEnConjonctionMultiplicativeDroite.
    reflexivity.
    set (pivot := (reductionListeMoleculesEnConjonctionMultiplicative [LMn])).
    simpl.
    eapply (coupureMoleculeP
              _ _ 1
              ((reductionListeMoleculesEnConjonctionMultiplicative prefLM)
                 ⊗ (pivot
                      ⊗ (reductionListeMoleculesEnConjonctionMultiplicative suffLM)))).
    simpl.
    eapply conjonctionMultiplicativeGaucheP.
    reflexivity.
    eapply (premierGaucheP _ _ 1).
    reflexivity.
    simpl.
    eapply conjonctionMultiplicativeGaucheP.
    reflexivity.
    eapply (conjonctionMultiplicativeDroiteP _ _ 1).
    reflexivity.
    simpl.
    apply equivalenceDefinitionEquivalenceMoleculaire.
    apply reflexiviteMoleculaire.
    eapply (premierGaucheP _ _ 1).
    reflexivity.
    simpl.
    eapply (conjonctionMultiplicativeDroiteP _ _ 1).
    reflexivity.
    simpl.
    apply equivalenceDefinitionEquivalenceMoleculaire.
    apply reflexiviteMoleculaire.
    apply equivalenceDefinitionEquivalenceMoleculaire.
    apply reflexiviteMoleculaire.
    simpl.
    apply equivalenceDefinitionEquivalenceMoleculaire.
    apply transitiviteMoleculaire with
        ((reductionListeMoleculesEnConjonctionMultiplicative prefLM)
           ⊗ (reductionListeMoleculesEnConjonctionMultiplicative ([LMn] ++ suffLM))).
    apply conjonctionMultiplicativeGauche.
    eapply (conjonctionMultiplicativeDroite 1).
    simpl.
    apply reflexiviteMoleculaire.
    simpl.
    apply conjonctionMultiplicativeGauche.
    apply (conjonctionMultiplicativeDroite 1).
    simpl.
    apply neutraliteDroiteMoleculaire.
    simpl.
    apply reflexiviteMoleculaire.
    apply reductionHomomorpheListeMoleculesEnConjonctionMultiplicativeGauche.
    symmetry.
    rewrite <- eqLMn.
    apply decompositionListeAvecPivot.
  }
Qed.

Proposition symmetrieMoleculaire :
  forall A,
  forall M1 M2: @Molecule A,
    EquivalenceMoleculaire [M1] M2
    -> EquivalenceMoleculaire [M2] M1.
Proof.
  intros A.
  intros M1 M2 EqM.
  apply transitiviteMoleculaire with  (M1 ⊗ un).
  apply equivalenceDefinitionEquivalenceMoleculaireP.
  apply equivalenceDefinitionEquivalenceMoleculaire in EqM.
  replace (M1 ⊗ un) with (reductionListeMoleculesEnConjonctionMultiplicative [M1]).
  apply symmetrieMoleculaireP.
  assumption.
  reflexivity.
  apply neutraliteDroiteMoleculaire.
Qed.

Proposition aucuneOccurrenceDansUnP :
  forall {A : Type}(a : A),
    OccurrenceP a un -> False.
Proof.
  intros A a occ.
  destruct occ as [eq | M1 M2 eq| M1 M2 eq];
    discriminate eq.
Qed.

Proposition equivalenceDefinitionOccurrence :
  forall A, forall a : A, forall M,
        Occurrence a M -> Habitation (OccurrenceP a M).
Proof.
  intros A a.
  fix HR 2.
  intros M occM.
  destruct occM as [| M1 M2 | M1 M2]. 
  {
    apply habitant.
    apply occurrenceAtomeP.
    reflexivity.
  }
  {
    destruct (HR M1 occM) as [occPM1].
    apply habitant.
    apply occurrenceConjonctionGaucheP with M1 M2.
    reflexivity.
    assumption.
  }
  {
    destruct (HR M2 occM) as [occPM2].
    apply habitant.
    apply occurrenceConjonctionDroiteP with M1 M2.
    reflexivity.
    assumption.
  }
Qed.

Proposition equivalenceDefinitionOccurrenceP :
  forall A, forall a : A, forall M,
        OccurrenceP a M -> Occurrence a M.
Proof.
  intros A a.
  fix HR 2.
  intros M occM.
  destruct occM as [eqA | M1 M2 eq| M1 M2 eq].
  {
    rewrite eqA.
    apply occurrenceAtome.
  }
  {
    rewrite eq.
    apply occurrenceConjonctionGauche.
    apply HR.
    assumption.
  }
  {
    rewrite eq.
    apply occurrenceConjonctionDroite.
    apply HR.
    assumption.
  }
Qed.

Proposition equivalenceDefinitionHabitationOccurrenceP :
  forall A, forall a : A, forall M,
        Habitation (OccurrenceP a M) -> Occurrence a M.
Proof.
  intros A a M [occM].
  apply equivalenceDefinitionOccurrenceP.
  assumption.
Qed.

Proposition aucuneOccurrenceDansUn :
  forall {A : Type}(a : A),
    Occurrence a un -> False.
Proof.
  intros A a occUN.
  apply equivalenceDefinitionOccurrence in occUN.
  destruct occUN.
  apply aucuneOccurrenceDansUnP with a.
  assumption.
Qed.

Proposition occurrenceAtomique :
  forall {A : Type}(a b: A),
    Occurrence a (atome b) -> a = b.
Proof.
  intro A.
  intros a b occ.
  apply equivalenceDefinitionOccurrence in occ.
  destruct occ as [occ].
  destruct occ as [eqA | M1 M2 eq| M1 M2 eq]; try (discriminate eq).
  {
    injection eqA.
    intro.
    symmetry.
    assumption.
  }
Qed.

Proposition occurrenceConjonction :
  forall {A : Type}(a : A) M1 M2,
    Occurrence a (M1 ⊗ M2) -> (Occurrence a M1 \/ Occurrence a M2).
Proof.
  intro A.
  intros a M1 M2 occ.
  apply equivalenceDefinitionOccurrence in occ.
  destruct occ as [occ].
  destruct occ as [eq | M1' M2' eq| M1' M2' eq]; try (discriminate eq).
  {
    injection eq.
    intros _ eqM1.
    rewrite <- eqM1 in occ.
    left.
    apply equivalenceDefinitionOccurrenceP.
    assumption.
  }
  {
    injection eq.
    intros eqM2 _.
    rewrite <- eqM2 in occ.
    right.
    apply equivalenceDefinitionOccurrenceP.
    assumption.
  }
Qed.

Proposition effacementEffectif :
  forall A : Type,
  forall a :A,
  forall M,
  forall Occ : OccurrenceP a M,
    effacementAtome a M Occ <> M.
Proof.
  intros A a.
  fix HR 2.
  intros M Occ Absurde.
  destruct Occ as [eqMa | M1 M2 eqM OccMG | M1 M2 eqM OccMD].
  {
    simpl in Absurde.
    rewrite eqMa in Absurde.
    discriminate Absurde.
  }
  {
    simpl in Absurde.
    rewrite eqM in Absurde.
    injection Absurde.
    intro Absurde'.
    apply (HR M1 OccMG Absurde').
  }
  {
    simpl in Absurde.
    rewrite eqM in Absurde.
    injection Absurde.
    intro Absurde'.
    apply (HR M2 OccMD Absurde').
  }
Qed.

Proposition effacementAtomeDansConjonctionMultiplicative :
  forall A : Type,
  forall a :A,
  forall M M1 M2,
  forall occ : OccurrenceP a M,
    M = M1 ⊗ M2
    ->
    (exists occ1 : OccurrenceP a M1,
        effacementAtome a M occ = (effacementAtome a M1 occ1) ⊗ M2)
    \/
    (exists occ2 : OccurrenceP a M2,
        effacementAtome a M occ =  M1 ⊗ (effacementAtome a M2 occ2)).
Proof.
  intros A a M M1 M2 occ eqM.
  destruct occ as 
      [eqMa | M1' M2' eqM' occ1 | M1' M2' eqM' occ2].
  {
    assert(atome a = M1 ⊗ M2) as Absurde.
    {
      transitivity M.
      symmetry; assumption.
      assumption.
    }
    discriminate Absurde.    
  }
  {
    left.
    assert(M1 ⊗ M2 = M1' ⊗ M2') as eqM12.
    {
      transitivity M.
      symmetry; assumption.
      assumption.
    }
    injection eqM12.
    intros eqM2 eqM1.
    rewrite eqM1.
    rewrite eqM2.
    exists occ1.
    destruct M; try (discriminate eqM).
    {
      simpl.
      reflexivity.
    }
  }
  {
    right.
    assert(M1 ⊗ M2 = M1' ⊗ M2') as eqM12.
    {
      transitivity M.
      symmetry; assumption.
      assumption.
    }
    injection eqM12.
    intros eqM2 eqM1.
    rewrite eqM1.
    rewrite eqM2.
    exists occ2.
    destruct M; try (discriminate eqM).
    {
      simpl.
      reflexivity.
    }
  }
Qed.

Proposition indifferenceOccurrenceAtome :
  forall (A : Type) (a : A) M N,
  forall occ : OccurrenceP a N,
    M = N
    ->
    EquivalenceMoleculaire
      [M]
      (atome a ⊗ (effacementAtome a N occ)).
Proof.
  intros A a.
  fix HR 1.
  intros M N occ eqMN.
  destruct M as [ | b | Ma Mb].
  {
    exfalso.
    apply aucuneOccurrenceDansUnP with a.
    rewrite eqMN.
    assumption.
  }
  {
    destruct occ as [eqAB | M1 M2 eqM Occ1 | M1 M2 eqM Occ2].
    {
      rewrite eqMN.
      rewrite eqAB.
      simpl.
      eapply (conjonctionMultiplicativeDroite 1).
      apply identiteAtome.
      apply unDroite.
    }
    {
      rewrite eqM in eqMN.
      discriminate eqMN.
    }
    {
      rewrite eqM in eqMN.
      discriminate eqMN.
    }
  }
  {
    destruct occ as [eqA | N1 N2 eqM Occ1 | N1 N2 eqM Occ2].
    {
      rewrite eqA in eqMN.
      discriminate eqMN.
    }
    {
      simpl.
      apply transitiviteMoleculaire with ((atome a ⊗ effacementAtome a N1 Occ1) ⊗ N2).
      apply conjonctionMultiplicativeGauche.
      eapply (conjonctionMultiplicativeDroite 1).
      simpl.
      apply HR.
      rewrite eqM in eqMN.
      injection eqMN.
      tauto.
      simpl.
      rewrite eqM in eqMN.
      injection eqMN.
      intros eqMbN2 _.
      rewrite eqMbN2.
      apply reflexiviteMoleculaire.
      apply associativiteGaucheMoleculaire.
    }
    {
      simpl.
      apply transitiviteMoleculaire with ((atome a ⊗ N1) ⊗ effacementAtome a N2 Occ2).
      apply transitiviteMoleculaire with ((N1 ⊗ atome a) ⊗ effacementAtome a N2 Occ2).
      apply transitiviteMoleculaire with (N1 ⊗ (atome a ⊗ effacementAtome a N2 Occ2)).
      apply conjonctionMultiplicativeGauche.
      eapply (conjonctionMultiplicativeDroite 1).
      simpl.
      rewrite eqM in eqMN.
      injection eqMN.
      intros _ eqMaN1.
      rewrite eqMaN1.
      apply reflexiviteMoleculaire.
      simpl.
      apply HR.
      rewrite eqM in eqMN.
      injection eqMN.
      tauto.
      apply associativiteDroiteMoleculaire.
      apply congruenceMoleculaire.
      apply commutativiteMoleculaire.
      apply reflexiviteMoleculaire.
      apply associativiteGaucheMoleculaire.
    }
  }
Qed.

Proposition indifferenceOccurrenceConjonction :
  forall (A : Type) (a : A) M1 M2 M1' M2',
  forall occ1 : OccurrenceP a M1',
  forall occ2 : OccurrenceP a M2',
    M1 = M1'
    -> M2 = M2'
    -> EquivalenceMoleculaire
         [(effacementAtome a M1' occ1) ⊗ M2]
         (M1 ⊗ (effacementAtome a M2' occ2)).
Proof.
  intros A a.
  fix HR 1.
  intros M1 M2 M1' M2' occ1 occ2 eqM1 eqM2.
  destruct M1 as [ | b | M1a M1b].
  {
    exfalso.
    apply aucuneOccurrenceDansUnP with a.
    rewrite eqM1.
    assumption.
  }
  {
    destruct occ1 as [eqAB | M1a' M1b' eqM Occa | M1a' M1b' eqM Occb].
    {
      rewrite eqAB.
      simpl.
      apply transitiviteMoleculaire with M2.
      apply neutraliteGaucheMoleculaire.
      rewrite eqM1.
      rewrite eqAB.
      apply indifferenceOccurrenceAtome.
      assumption.
    }
    {
      rewrite eqM in eqM1.
      discriminate eqM1.
    }
    {
      rewrite eqM in eqM1.
      discriminate eqM1.
    }
  }
  {
    destruct occ1 as [eqAt | M1a' M1b' eqM Occa | M1a' M1b' eqM Occb].
    {
      rewrite eqAt in eqM1.
      discriminate eqM1.
    }
    {
      simpl.
      apply transitiviteMoleculaire with (effacementAtome a M1a' Occa ⊗ (M1b' ⊗ M2)).
      apply associativiteGaucheMoleculaire.
      apply transitiviteMoleculaire with (M1a ⊗ (M1b ⊗ effacementAtome a M2' occ2)).
      rewrite eqM in eqM1.
      injection eqM1.
      intros eqM1b eqM1a.
      apply transitiviteMoleculaire with
          (M1a ⊗
               (effacementAtome a (M1b ⊗ M2') (occurrenceConjonctionDroiteP a _ M1b M2' eq_refl occ2))).
      apply HR.
      assumption.
      f_equal.
      symmetry; assumption.
      assumption.
      apply congruenceMoleculaire.
      apply reflexiviteMoleculaire.
      simpl.
      apply reflexiviteMoleculaire.
      apply associativiteDroiteMoleculaire.
    }
    {
      simpl.
      rewrite eqM in eqM1.
      injection eqM1.
      intros eqM1b eqM1a.
      apply transitiviteMoleculaire with
          (effacementAtome a M1b' Occb ⊗ M1a' ⊗ M2).
      apply congruenceMoleculaire.
      apply commutativiteMoleculaire.
      apply reflexiviteMoleculaire.
      apply transitiviteMoleculaire with (M1b ⊗ M1a ⊗ effacementAtome a M2' occ2).
      apply transitiviteMoleculaire with (M1b ⊗ (M1a ⊗ effacementAtome a M2' occ2)).
      apply transitiviteMoleculaire with
          (effacementAtome a M1b' Occb ⊗ (M1a' ⊗ M2)).
      apply associativiteGaucheMoleculaire.
      apply transitiviteMoleculaire with
          (M1b ⊗
               (effacementAtome a (M1a ⊗ M2') (occurrenceConjonctionDroiteP a _ M1a M2' eq_refl occ2))).
      apply HR.
      assumption.
      f_equal.
      symmetry; assumption.
      assumption.      
      apply congruenceMoleculaire.
      apply reflexiviteMoleculaire.
      simpl.
      apply reflexiviteMoleculaire.
      apply associativiteDroiteMoleculaire.
      apply congruenceMoleculaire.
      apply commutativiteMoleculaire.
      apply reflexiviteMoleculaire.
    }
  }    
Qed.

Lemma simplificationAtomiqueExistentielleP :
  forall A,
  forall a : A,
  forall LM : list (@Molecule A),
  forall LM1 P LM2,
  forall M : @Molecule A,
  forall occG : (OccurrenceP a P),
    LM = LM1 ++ [P] ++ LM2
    -> EquivalenceMoleculaireP LM M
    -> exists M' (occ : (OccurrenceP a M')),
        M = M'
        /\
        EquivalenceMoleculaireP
          (LM1 ++ [effacementAtome a P occG] ++ LM2)
          (effacementAtome a M' occ).
Proof.
  intros A a.
  fix HR 8.
  intros LM LM1 P LM2 M occG eq_LM equiv_LM_M.
  destruct equiv_LM_M as [ b eqG eqD |  eqG eqD
                           | LM' eqG equivPrem | g M1 M2 eqM equivPrem1 equivPrem2
                           | LM' M1 M2 eqG equivPrem
                    | n LMn eqLMn equivPremier ] eqn:cas.
  {
    assert(P = atome b /\ LM1 = [] /\ LM2 = []) as [eqP [eqLM1 eqLM2]].
    {
      eapply simplificationSingleton.
      transitivity LM.
      symmetry.
      assumption.
      assumption.
    }
    rewrite eqLM1.
    rewrite eqLM2.
    simpl.
    exists P.
    exists occG.
    split.
    {
      transitivity (atome b).
      assumption.
      symmetry; assumption.
    }
    destruct occG as [eqMa | M1 M2 eqM Occ1 | M1 M2 eqM Occ2].
    {
      simpl.
      apply equivalenceDefinitionEquivalenceMoleculaire.
      apply reflexiviteMoleculaire.
    }
    {
      assert(atome b = M1 ⊗ M2) as Absurde.
      transitivity P.
      symmetry.
      assumption.
      assumption.
      discriminate Absurde.
    }
    {
      assert(atome b = M1 ⊗ M2) as Absurde.
      transitivity P.
      symmetry.
      assumption.
      assumption.
      discriminate Absurde.
    }
  }      
  {
    exfalso.
    rewrite eqG in eq_LM.
    destruct LM1; discriminate eq_LM.
  }
  {
    destruct LM1 as [ | tLM1 rLM1].
    {
      exfalso.
      rewrite eqG in eq_LM.
      simpl in eq_LM.
      injection eq_LM.
      intros _ eqP.
      rewrite <- eqP in occG.
      apply aucuneOccurrenceDansUnP with a.
      assumption.
    }
    {
      rewrite eqG in eq_LM.
      simpl in eq_LM.
      injection eq_LM.
      intros eq_LM' eq_tLM1.
      destruct (HR LM' rLM1 P LM2 M occG eq_LM') as [M' [occ [eqM EquivHR]]].
      assumption.
      exists M'.
      exists occ.
      split.
      assumption.
      rewrite <- eq_tLM1.
      apply unGaucheP with (rLM1 ++ [effacementAtome a P occG] ++ LM2).
      simpl.
      reflexivity.
      assumption.
    }
  }
  {
    (* conjonction multi droite *)
    assert (EquivalenceMoleculaireP (prefixe g LM) M1) as equivPrem1'.
    {
      assumption.
    }
    assert (EquivalenceMoleculaireP (suffixe g LM) M2) as equivPrem2'.
    {
      assumption.
    }
    rewrite eq_LM in equivPrem1'.
    rewrite eq_LM in equivPrem2'.
    destruct (g - length LM1) as [ | gMlLM1] eqn:eq_gMlLM1.
    {
      rewrite (prefixeAvantListeBipartite g) in equivPrem1'; try assumption.
      rewrite (suffixeAvantListeBipartite g) in equivPrem2'; try assumption.
      destruct (HR _ (suffixe g LM1) P LM2 M2 occG eq_refl equivPrem2') as [M2' [occ [eqM2 EquivHR]]].
      exists (M1 ⊗ M2').
      exists (occurrenceConjonctionDroiteP a _ M1 M2' eq_refl occ). 
      rewrite eqM.
      split.
      {
        rewrite eqM2.
        reflexivity.
      }
      {
        eapply (conjonctionMultiplicativeDroiteP _ _ g).
        simpl.
        reflexivity.
        rewrite (prefixeAvantListeBipartite g); try assumption.
        rewrite (suffixeAvantListeBipartite g); try assumption.
      }
    }
    {
      rewrite (prefixeApresListeBipartite g) in equivPrem1';
        try (apply (opposeSoustractionNonNulle _ _ _ eq_gMlLM1)).
      rewrite eq_gMlLM1 in equivPrem1'.
      simpl in equivPrem1'.
      rewrite (suffixeApresListeBipartite g) in equivPrem2';
        try (apply (opposeSoustractionNonNulle _ _ _ eq_gMlLM1)).
      rewrite eq_gMlLM1 in equivPrem2'.
      simpl in equivPrem2'.
      destruct (HR _ LM1 P (prefixe gMlLM1 LM2) M1 occG eq_refl equivPrem1')
        as [M1' [occ [eqM1 EquivHR]]].
      exists (M1' ⊗ M2).
      exists (occurrenceConjonctionGaucheP a _ M1' M2 eq_refl occ). 
      rewrite eqM.
      split.
      {
        rewrite eqM1.
        reflexivity.
      }
      {
        eapply (conjonctionMultiplicativeDroiteP _ _ g).
        simpl.
        reflexivity.
        rewrite (prefixeApresListeBipartite g);
          try (apply (opposeSoustractionNonNulle _ _ _ eq_gMlLM1)).
        rewrite eq_gMlLM1.
        simpl.
        assumption.
        rewrite (suffixeApresListeBipartite g);
          try (apply (opposeSoustractionNonNulle _ _ _ eq_gMlLM1)).
        rewrite eq_gMlLM1.
        simpl.
        assumption.
      }
    }
  }
  {
    destruct LM1 as [ | tLM1 rLM1].
    {
      simpl.
      rewrite eqG in eq_LM.
      simpl in eq_LM.
      injection eq_LM.
      intros eq_LM' eqP.
      destruct (effacementAtomeDansConjonctionMultiplicative 
                  _ a P M1 M2 occG (eq_sym eqP)) as [[occM1 eqEMG] | [occM2 eqEMD]].
      {
        rewrite eqEMG.
        rewrite <- eq_LM'.
        destruct (HR (M1 :: M2 :: LM') [] M1 (M2 :: LM') M occM1 eq_refl equivPrem)
          as [M' [occ [eqM' EquivHR]]].
        exists M'.
        exists occ.
        split.
        assumption.
        simpl.
        simpl in EquivHR.
        eapply conjonctionMultiplicativeGaucheP.
        reflexivity.
        assumption.
      }
      {
        rewrite eqEMD.
        rewrite <- eq_LM'.
        destruct (HR (M1 :: M2 :: LM') [M1] M2 LM' M occM2 eq_refl equivPrem)
          as [M' [occ [eqM' EquivHR]]].
        exists M'.
        exists occ.
        split.
        assumption.
        simpl.
        simpl in EquivHR.
        eapply conjonctionMultiplicativeGaucheP.
        reflexivity.
        assumption. 
      }
    }
    {
      rewrite eqG in eq_LM.
      injection eq_LM.
      intros eqLM' eqTLM1.
      simpl.
      rewrite <- eqTLM1.      
      destruct (HR (M1 :: M2 :: LM') (M1 :: M2 :: rLM1) P LM2 M occG)
          as [M' [occ [eqM' EquivHR]]].
      simpl.
      rewrite eqLM'.
      reflexivity.
      assumption.
      exists M'.
      exists occ.
      split.
      {
        assumption.
      }
      {
        eapply conjonctionMultiplicativeGaucheP.
        reflexivity.
        assumption.
      }
    }
  }
  {
    (* cas premierGauche *)
    simpl in eq_LM.
    assert(EquivalenceMoleculaireP (LMn :: prefixe n LM ++ suffixe (S n) LM) M) as equivPremier'.
    {
      assumption.
    }
    rewrite eq_LM in equivPremier'.
    assert(valeur n LM = [LMn]) as eqLMn'.
    {
      assumption.
    }
    rewrite eq_LM in eqLMn'.
    destruct (n - length LM1) as [ | pnMlLM1] eqn:eq_nMlLM1.
    {
      destruct (S n - length LM1) as [ | pSnMlLM1] eqn:eq_SnMlLM1.      
      {
        rewrite (valeurAvantListeTripartite n) in eqLMn'; try assumption.
        rewrite (prefixeAvantListeTripartite n) in equivPremier'; try assumption.
        rewrite (suffixeAvantListeTripartite (S n)) in equivPremier'; try assumption.
        destruct (HR _
                     (LMn :: prefixe n LM1 ++ suffixe (S n) LM1)
                     P LM2
                     M
                     occG
                     eq_refl) as [M' [occ [eqM' EquivHR]]].
        simpl.
        replace (LMn :: (prefixe n LM1 ++ suffixe (S n) LM1) ++ P :: LM2) with
            (LMn :: prefixe n LM1 ++ suffixe (S n) LM1 ++ P :: LM2).
        assumption.
        egaliteListes.        
        exists M'.
        exists occ.
        split.
        {
          assumption.
        }
        {
          eapply (premierGaucheP _ _ n LMn).
          simpl.
          rewrite (valeurAvantListeTripartite n); try assumption.
          simpl.
          rewrite (prefixeAvantListeTripartite n); try assumption.
          rewrite (suffixeAvantListeTripartite (S n)); try assumption.
          replace (LMn :: prefixe n LM1 ++ suffixe (S n) LM1 ++ effacementAtome a P occG :: LM2)
            with ((LMn :: prefixe n LM1 ++ suffixe (S n) LM1) ++ [effacementAtome a P occG] ++ LM2).
          assumption.
          egaliteListes.
        }
      }
      {
        assert((n = length LM1) /\ (pSnMlLM1 = 0)) as [eqNlLM1 eqpSnMlLM1].
        {
          apply casEgaliteSoustractionNulle; assumption.
        }
        rewrite (valeurPivotListeTripartite n) in eqLMn'; try assumption.
        rewrite (prefixePivotListeTripartite n) in equivPremier'; try assumption.
        rewrite (suffixeApresListeTripartite (S n) pSnMlLM1) in equivPremier'; try assumption.
        replace (LMn :: LM1 ++ suffixe pSnMlLM1 LM2) with
            ([] ++ [P] ++ (LM1 ++ suffixe pSnMlLM1 LM2)) in equivPremier'. 
        destruct (HR _
                     []
                     P
                     _
                     M
                     occG
                     eq_refl
                     equivPremier') as [M' [occ [eqM' EquivHR]]].
        exists M'.
        exists occ.
        split.
        {
          assumption.
        }
        {
          eapply (premierGaucheP _ _ n (effacementAtome a P occG)).
          simpl.
          rewrite (valeurPivotListeTripartite n); try assumption.
          reflexivity.
          simpl.
          rewrite (prefixePivotListeTripartite n); try assumption.
          rewrite (suffixeApresListeTripartite (S n) pSnMlLM1); try assumption.
        }
        injection eqLMn'; intro eqPivot.
        rewrite eqPivot.
        egaliteListes.
      }
    }
    {
      rewrite (valeurApresListeTripartite n pnMlLM1) in eqLMn';
        try assumption.
      rewrite (prefixeApresListeTripartite n pnMlLM1) in equivPremier';
        try assumption.
      rewrite (suffixeApresListeTripartite (S n) (S pnMlLM1)) in equivPremier';
        try assumption.
      replace (LMn :: (LM1 ++ P :: prefixe pnMlLM1 LM2) ++ suffixe (S pnMlLM1) LM2)
        with ((LMn :: LM1) ++ [P] ++ (prefixe pnMlLM1 LM2 ++ suffixe (S pnMlLM1) LM2))
      in equivPremier'.
      destruct (HR _
                   _ 
                   _
                   _
                   M
                   occG
                   eq_refl
                   equivPremier') as [M' [occ [eqM' EquivHR]]].
      simpl.
      exists M'.
      exists occ.
      split.
      {
          assumption.
      }
      {
        eapply (premierGaucheP _ _ n LMn).
        rewrite (valeurApresListeTripartite n pnMlLM1);
          try assumption.
        rewrite (prefixeApresListeTripartite n pnMlLM1);
          try assumption.
        rewrite (suffixeApresListeTripartite (S n) (S pnMlLM1));
          try assumption.
        replace
          (LMn :: (LM1 ++ effacementAtome a P occG :: prefixe pnMlLM1 LM2) ++ suffixe (S pnMlLM1) LM2)
          with
            ((LMn :: LM1) ++
                          [effacementAtome a P occG] ++ prefixe pnMlLM1 LM2 ++ suffixe (S pnMlLM1) LM2).
        assumption.
        egaliteListes.              
        apply successeurSoustractionNonNulle; assumption.
      }
      egaliteListes.
      apply successeurSoustractionNonNulle; assumption.
    }
  }
Qed.

Lemma simplificationAtomiqueP :
  forall A,
  forall a : A,
  forall LM : list (@Molecule A),
  forall LM1 P LM2,
  forall M : @Molecule A,
  forall occG : (OccurrenceP a P),
  forall occ : OccurrenceP a M,
    LM = LM1 ++ [P] ++ LM2
    -> EquivalenceMoleculaireP LM M
    -> EquivalenceMoleculaireP
         (LM1 ++ [effacementAtome a P occG] ++ LM2)
         (effacementAtome a M occ).
Proof.
  intros A a.
  fix HR 9.
  intros LM LM1 P LM2 M occG occ eq_LM equiv_LM_M.
  destruct equiv_LM_M as [ b eqG eqD | eqG eqD
                           | LM' eqG equivPrem | g M1 M2 eqM equivPrem1 equivPrem2
                           | LM' M1 M2 eqG equivPrem
                           | ] eqn:cas.
  {
    assert(P = atome b /\ LM1 = [] /\ LM2 = []) as [eqP [eqLM1 eqLM2]].
    {
      eapply simplificationSingleton.
      transitivity LM.
      symmetry.
      assumption.
      assumption.
    }
    rewrite eqLM1.
    rewrite eqLM2.
    simpl.
    destruct occG as [eqMa | M1 M2 eqM Occ1 | M1 M2 eqM Occ2].
    {
      destruct occ as [eqMa' | M1' M2' eqM' Occ1' | M1' M2' eqM' Occ2'].
      {
        simpl.
        apply equivalenceDefinitionEquivalenceMoleculaire.
        apply reflexiviteMoleculaire.
      }
      {
        assert(atome b = M1' ⊗ M2') as Absurde.
        transitivity M.
        symmetry.
        assumption.
        assumption.
        discriminate Absurde.
      }
      {
        assert(atome b = M1' ⊗ M2') as Absurde.
        transitivity M.
        symmetry.
        assumption.
        assumption.
        discriminate Absurde.
      }
    }
    {
      assert(atome b = M1 ⊗ M2) as Absurde.
      transitivity P.
      symmetry.
      assumption.
      assumption.
      discriminate Absurde.
    }
    {
      assert(atome b = M1 ⊗ M2) as Absurde.
      transitivity P.
      symmetry.
      assumption.
      assumption.
      discriminate Absurde.
    }
  }
  {
    exfalso.
    rewrite eqG in eq_LM.
    destruct LM1; discriminate eq_LM.
  }
  {
    destruct LM1 as [ | tLM1 rLM1].
    {
      exfalso.
      rewrite eqG in eq_LM.
      simpl in eq_LM.
      injection eq_LM.
      intros _ eqP.
      rewrite <- eqP in occG.
      apply aucuneOccurrenceDansUnP with a.
      assumption.
    }
    {
      rewrite eqG in eq_LM.
      simpl in eq_LM.
      injection eq_LM.
      intros eq_LM' eq_tLM1.
      rewrite <- eq_tLM1.
      apply unGaucheP with (rLM1 ++ [effacementAtome a P occG] ++ LM2).
      simpl.
      reflexivity.
      apply (HR LM' rLM1 P LM2 M occG).
      assumption.
      assumption.
    }
  }
  {
    (* conjonction multi droite 
     *
     *  LM[:g[ ⊢ M1   LM[g:[ ⊢ M2
     *  -------------------------
     *       LM ⊢ M1 ⊗ M2  
     * cas problématiques
     *  - a dans LM[:g[, a dans M2
     *  - a dans LM[g:[, a dans M1
     *) 
    (* conjonction multi droite *)
    assert( EquivalenceMoleculaireP (prefixe g LM) M1) as equivPrem1'.
    {
      assumption.
    }
    assert( EquivalenceMoleculaireP (suffixe g LM) M2) as equivPrem2'.
    {
      assumption.
    }
    rewrite eq_LM in equivPrem2'.
    rewrite eq_LM in equivPrem1'.
    simpl in equivPrem1'.
    simpl in equivPrem2'.
    destruct (g - length LM1) as [ | gMlLM1] eqn:eq_gMlLM1.
    { (* pivot à droite, *)
      rewrite (prefixeAvantListeBipartite g) in equivPrem1';
        try assumption.
      rewrite (suffixeAvantListeBipartite g) in equivPrem2';
        try assumption.
      destruct (effacementAtomeDansConjonctionMultiplicative 
                  _ a M M1 M2 occ eqM) as [[occM1 eqEMG] | [occM2 eqEMD]].
      { (* occurrence à gauche *)
        destruct (simplificationAtomiqueExistentielleP A a _
                   (suffixe g LM1) P LM2 M2 occG eq_refl equivPrem2'
                 ) as [M2' [occM2' [eqM2 EquivD]]].
        apply (coupureMoleculeP _ _
                 (length (LM1 ++ [effacementAtome a P occG] ++ LM2))
                 (M1 ⊗ effacementAtome a M2' occM2')).
        eapply (conjonctionMultiplicativeDroiteP _ _ g).
        reflexivity.
        rewrite prefixeEnFin.
        simpl.
        rewrite (prefixeAvantListeBipartite g);
          try assumption.
        rewrite prefixeEnFin.
        rewrite (suffixeAvantListeBipartite g);
          try assumption.
        simpl.
        rewrite suffixeEnFin.
        rewrite eqEMG.
        apply equivalenceDefinitionEquivalenceMoleculaire.
        apply symmetrieMoleculaire.
        apply indifferenceOccurrenceConjonction.
        reflexivity.
        assumption.
      }
      { (* occurrence à droite *)
        rewrite eqEMD.
        eapply (conjonctionMultiplicativeDroiteP _ _ g).
        reflexivity.
        rewrite (prefixeAvantListeBipartite g);
          try assumption.
        rewrite (suffixeAvantListeBipartite g);
          try assumption.
        apply (HR _ (suffixe g LM1) P LM2 M2 occG occM2 eq_refl).        
        assumption.
      }
    }
    { (* pivot à gauche *)
      rewrite (prefixeApresListeTripartite g gMlLM1) in equivPrem1';
        try assumption.
      rewrite (suffixeApresListeTripartite g gMlLM1) in equivPrem2';
        try assumption.
      destruct (effacementAtomeDansConjonctionMultiplicative 
                  _ a M M1 M2 occ eqM) as [[occM1 eqEMG] | [occM2 eqEMD]].
      { (* occurrence à gauche *)
        rewrite eqEMG.
        eapply (conjonctionMultiplicativeDroiteP _ _ g).
        reflexivity.
        simpl.
        rewrite (prefixeApresListeTripartite g gMlLM1);
          try assumption.
        apply (HR _ LM1 P (prefixe gMlLM1 LM2)
                  M1 occG occM1 eq_refl).        
        assumption.
        simpl.
        rewrite (suffixeApresListeTripartite g gMlLM1);
          try assumption.
      }
      { (* occurrence à droite *)
        destruct (simplificationAtomiqueExistentielleP A a _
                   LM1 P (prefixe gMlLM1 LM2) M1 occG eq_refl equivPrem1'
                 ) as [M1' [occM1' [eqM1 EquivG]]].
        apply (coupureMoleculeP _ _
                 (length (LM1 ++ [effacementAtome a P occG] ++ LM2))
                 (effacementAtome a M1' occM1' ⊗ M2)).
        eapply (conjonctionMultiplicativeDroiteP _ _ g).
        reflexivity.        
        rewrite prefixeEnFin.
        simpl.
        rewrite (prefixeApresListeTripartite g gMlLM1);
          try assumption.
        rewrite prefixeEnFin.
        simpl.
        rewrite (suffixeApresListeTripartite g gMlLM1);
          try assumption.
        simpl.
        rewrite suffixeEnFin.
        rewrite eqEMD.
        apply equivalenceDefinitionEquivalenceMoleculaire.
        apply indifferenceOccurrenceConjonction.
        assumption.
        reflexivity.
      }
    }
  }
  {
    destruct LM1 as [ | tLM1 rLM1].
    {
      simpl.
      rewrite eqG in eq_LM.
      simpl in eq_LM.
      injection eq_LM.
      intros eq_LM' eqP.
      destruct (effacementAtomeDansConjonctionMultiplicative 
                  _ a P M1 M2 occG (eq_sym eqP)) as [[occM1 eqEMG] | [occM2 eqEMD]].
      {
        rewrite eqEMG.
        eapply conjonctionMultiplicativeGaucheP.
        reflexivity.
        rewrite <- eq_LM'.
        apply (HR (M1 :: M2 :: LM') [] M1 (M2 :: LM') M occM1 occ eq_refl equivPrem).
      }
      {
        rewrite eqEMD.
        eapply conjonctionMultiplicativeGaucheP.
        reflexivity.
        rewrite <- eq_LM'.
        apply (HR (M1 :: M2 :: LM') [M1] M2 LM' M occM2 occ eq_refl equivPrem).
      } 
    }
    {
      rewrite eqG in eq_LM.
      injection eq_LM.
      intros eqLM' eqTLM1.
      simpl.
      rewrite <- eqTLM1.
      eapply conjonctionMultiplicativeGaucheP.
      reflexivity.
      apply (HR (M1 :: M2 :: LM') (M1 :: M2 :: rLM1) P LM2 M occG occ).
      simpl.
      rewrite eqLM'.
      reflexivity.
      assumption.
    }
  }
  {
    (* cas premierGauche *)
    assert(EquivalenceMoleculaireP (LMn :: prefixe n LM ++ suffixe (S n) LM) M) as equivPremier'.
    {
      assumption.
    }
    rewrite eq_LM in equivPremier'.
    simpl in equivPremier'.
    assert(valeur n LM = [LMn]) as eqLMn'.
    {
      assumption.
    }
    rewrite eq_LM in eqLMn'.
    simpl in eqLMn'.
    destruct (n - length LM1) as [ | pnMlLM1] eqn:eq_nMlLM1.
    {
      destruct (S n - length LM1) as [ | pSnMlLM1] eqn:eq_SnMlLM1.      
      {
        rewrite (valeurAvantListeTripartite n) in eqLMn'; try assumption.
        rewrite (prefixeAvantListeTripartite n) in equivPremier'; try assumption.
        rewrite (suffixeAvantListeTripartite (S n)) in equivPremier'; try assumption.
        eapply (premierGaucheP _ _ n LMn).
        simpl.
        rewrite (valeurAvantListeTripartite n); try assumption.
        simpl.
        rewrite (prefixeAvantListeTripartite n); try assumption.
        rewrite (suffixeAvantListeTripartite (S n)); try assumption.
        replace 
          (LMn :: prefixe n LM1 ++ suffixe (S n) LM1 ++ effacementAtome a P occG :: LM2)
          with
            ((LMn :: prefixe n LM1 ++ suffixe (S n) LM1) ++ effacementAtome a P occG :: LM2).
        apply (HR _
                  (LMn :: prefixe n LM1 ++ suffixe (S n) LM1)
                  P LM2
                  M
                  occG
                  occ
                  eq_refl).
        simpl.
        replace
          (LMn :: (prefixe n LM1 ++ suffixe (S n) LM1) ++ P :: LM2)
          with
            (LMn :: prefixe n LM1 ++ suffixe (S n) LM1 ++ P :: LM2).
        assumption.
        egaliteListes.
        egaliteListes.
      }
      {
        assert((n = length LM1) /\ (pSnMlLM1 = 0)) as [eqNlLM1 eqpSnMlLM1].
        {
          apply casEgaliteSoustractionNulle; assumption.
        }
        rewrite (valeurPivotListeTripartite n) in eqLMn'; try assumption.
        rewrite (prefixePivotListeTripartite n) in equivPremier'; try assumption.
        rewrite (suffixeApresListeTripartite (S n) 0) in equivPremier'; try assumption.
        rewrite suffixeEnZero in equivPremier'; try assumption.
        eapply (premierGaucheP _ _ n (effacementAtome a P occG)).
        simpl.
        rewrite (valeurPivotListeTripartite n); try assumption.
        reflexivity.
        simpl.
        rewrite (prefixePivotListeTripartite n); try assumption.
        rewrite (suffixeApresListeTripartite (S n) 0); try assumption.
        rewrite suffixeEnZero; try assumption.
        simpl.
        replace (effacementAtome a P occG :: LM1 ++ suffixe pSnMlLM1 LM2)
          with ([] ++ [effacementAtome a P occG] ++ (LM1 ++ suffixe pSnMlLM1 LM2)).
        apply (HR _
                  []
                  P
                  _
                  M
                  occG
                  occ
                  eq_refl).
        simpl.
        injection eqLMn'; intro eqPivot.        
        rewrite eqPivot.
        assumption.
        egaliteListes.
        rewrite eqpSnMlLM1 in eq_SnMlLM1.
        assumption.
        rewrite eqpSnMlLM1 in eq_SnMlLM1.
        assumption.
      }
    }        
    {
      rewrite (valeurApresListeTripartite n pnMlLM1) in eqLMn'; try assumption.
      rewrite (prefixeApresListeTripartite n pnMlLM1) in equivPremier'; try assumption.
      rewrite (suffixeApresListeTripartite (S n) (S pnMlLM1)) in equivPremier'; try assumption.
      eapply (premierGaucheP _ _ n LMn).
      simpl.
      rewrite (valeurApresListeTripartite n pnMlLM1); try assumption.
      simpl.
      rewrite (prefixeApresListeTripartite n pnMlLM1); try assumption.
      rewrite (suffixeApresListeTripartite (S n) (S pnMlLM1)); try assumption.
      replace
        (LMn :: (LM1 ++ effacementAtome a P occG :: prefixe pnMlLM1 LM2)
             ++ suffixe (S pnMlLM1) LM2)
        with
          ((LMn :: LM1)
             ++ [effacementAtome a P occG]
             ++ (prefixe pnMlLM1 LM2 ++ suffixe (S pnMlLM1) LM2)).
      apply
          (HR _
              _
              _
              _
              M
              occG
              occ
              eq_refl).
      replace
        ((LMn :: LM1) ++ [P] ++ prefixe pnMlLM1 LM2 ++ suffixe (S pnMlLM1) LM2)
        with
          (LMn :: (LM1 ++ P :: prefixe pnMlLM1 LM2) ++ suffixe (S pnMlLM1) LM2).
      assumption.
      egaliteListes.
      egaliteListes.
      apply successeurSoustractionNonNulle; assumption.
      apply successeurSoustractionNonNulle; assumption.
    }
  }
Qed.

Lemma simplicationAtomiqueGauche :
  forall A,
  forall a,
  forall N1 N2 : @Molecule A,
    EquivalenceMoleculaire [(atome a) ⊗ N1] ((atome a) ⊗ N2)
    -> EquivalenceMoleculaire [N1] N2.
Proof.
  intros A a N1 N2 equiv.
  apply transitiviteMoleculaire with (un ⊗ N1).
  eapply (conjonctionMultiplicativeDroite 0).
  apply unDroite.
  simpl.
  apply reflexiviteMoleculaire.
  apply transitiviteMoleculaire with (un ⊗ N2).  
  apply equivalenceDefinitionEquivalenceMoleculaireP.
  apply equivalenceDefinitionEquivalenceMoleculaire in equiv.
  replace [un ⊗ N1] with
      (prefixe 0 [atome a ⊗ N1]
               ++ [effacementAtome a (atome a ⊗ N1) (occurrenceAtomePGauche a N1)]
               ++ suffixe 1 [atome a ⊗ N1]).
  replace (un ⊗ N2) with (effacementAtome a (atome a ⊗ N2)  (occurrenceAtomePGauche a N2)).
  eapply simplificationAtomiqueP.
  reflexivity.
  assumption.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  apply conjonctionMultiplicativeGauche.
  apply unGauche.
  apply reflexiviteMoleculaire.
Qed.

Proposition simplicationMoleculaireGauche :
  forall A,
  forall M N1 N2 : @Molecule A,
    EquivalenceMoleculaire [M ⊗ N1] (M ⊗ N2)
    -> EquivalenceMoleculaire [N1] N2.
Proof.
  intro A.
  fix HR 1.
  intros M N1 N2 eqMN.
  destruct M as [ | a | M1 M2] eqn:cas.
  {
    apply transitiviteMoleculaire with (un ⊗ N1).
    apply symmetrieMoleculaire.
    apply neutraliteGaucheMoleculaire.
    apply transitiviteMoleculaire with (un ⊗ N2).
    assumption.
    apply neutraliteGaucheMoleculaire.
  }
  {
    apply simplicationAtomiqueGauche with a.
    assumption.
  }
  {
    assert(EquivalenceMoleculaire [M2 ⊗ N1] (M2 ⊗ N2)).
    apply (HR M1).
    apply transitiviteMoleculaire with (M1 ⊗ M2 ⊗ N1).
    apply associativiteDroiteMoleculaire.
    apply transitiviteMoleculaire with (M1 ⊗ M2 ⊗ N2).
    assumption.
    apply associativiteGaucheMoleculaire.
    apply (HR M2).
    assumption.
  }
Qed.

Proposition simplicationMoleculaireDroite :
  forall A,
  forall M N1 N2 : @Molecule A,
    EquivalenceMoleculaire [N1 ⊗ M] (N2 ⊗ M)
    -> EquivalenceMoleculaire [N1] N2.
Proof.
  intro A.
  intros M N1 N2 eqNM.
  assert(EquivalenceMoleculaire [M ⊗ N1] (M ⊗ N2)) as eqMN.
  apply transitiviteMoleculaire with (N1 ⊗ M).
  apply commutativiteMoleculaire.
  apply transitiviteMoleculaire with (N2 ⊗ M).
  assumption.
  apply commutativiteMoleculaire.
  apply simplicationMoleculaireGauche with M.
  assumption.
Qed.

Proposition absenceSansOccurrence :
  forall A : Type,
  forall M : @Molecule A,
  forall a : A,
    Absence M a <-> ~(Occurrence a M).
Proof.
  intro A.
  fix HR 1.
  intros M a.
  destruct M as [ | b | M1 M2].
  {
    simpl.
    split.
    intro.
    intro.
    apply aucuneOccurrenceDansUn with a.
    assumption.
    intro.
    exact I.
  }
  {
    simpl.
    split.
    {
      intro ineqA.
      intro occA.
      apply occurrenceAtomique in occA.
      exact (ineqA occA).
    }
    {
      intro negOcc.
      intro eqAB.
      rewrite eqAB in negOcc.
      exact (negOcc (occurrenceAtome b)).
    }
  }
  {
    split.
    {
      simpl.
      intros [Abs1 Abs2].
      intro occ.
      apply occurrenceConjonction in occ.
      destruct occ as [occ | occ].
      {
        apply (proj1 (HR M1 a)).
        assumption.
        assumption.
      }
      {
        apply (proj1 (HR M2 a)).
        assumption.
        assumption.
      }
    }
    {
      intro negOcc.
      simpl.
      split.
      {
        apply (proj2 (HR M1 a)).
        intro occM1.
        apply (occurrenceConjonctionGauche _ M1 M2) in occM1.
        exact (negOcc occM1).
      }
      {
        apply (proj2 (HR M2 a)).
        intro occM2.
        apply (occurrenceConjonctionDroite _ M1 M2) in occM2.
        exact (negOcc occM2).
      }
    }
  }
Qed.

Proposition compatibiliteAbsenceEquivalenceMoleculaire :
  forall A : Type,
  forall M1 M2 : @Molecule A,
  forall a : A,
    Absence M1 a -> EquivalenceMoleculaire [M1] M2 -> Absence M2 a.
Proof.
  intros A M1 M2 a Abs1 Equiv.
  apply absenceSansOccurrence.
  intro occ2.
  apply equivalenceDefinitionOccurrence in occ2.
  destruct occ2 as [occ2].
  apply symmetrieMoleculaire in Equiv.
  apply equivalenceDefinitionEquivalenceMoleculaire in Equiv.
  destruct 
    (simplificationAtomiqueExistentielleP
       _
       a
       [M2]
       []
       M2
       []
       M1
       occ2
       eq_refl
       Equiv) as [M1' [occ1 [eqM1 _]]].
  rewrite <- eqM1 in occ1.
  apply equivalenceDefinitionOccurrenceP in occ1.
  apply absenceSansOccurrence in Abs1.
  exact (Abs1 occ1).
Qed.

Lemma AbsenceNotPresence : forall A M X, 
                                                      @Absence A M X <->  ~ (@Presence A M X).
Proof.
  split; try unfold not; intros; induction M; simpl in *.
  destruct H0.
  destruct H; assumption.
  destruct H; destruct H0.
  apply IHM1; assumption.
  apply IHM2; assumption.
  trivial.
  assumption.
  split.
  apply IHM1; intros.
  apply H.
  left; assumption.
  apply IHM2; intros.
  apply H.
  right; assumption.
Qed.

Lemma OccurrenceEquivPresence : forall A M X,
  @Presence A M X <->  @Occurrence A X M.
Proof.
  split; intros.
  induction M; simpl in *.
  destruct H.
  subst.
  apply occurrenceAtome.
  destruct H.
  apply occurrenceConjonctionGauche.
  apply IHM1; trivial.
  apply occurrenceConjonctionDroite.
  apply IHM2; trivial.
  induction M; simpl in *.
  destruct (aucuneOccurrenceDansUn X); trivial.
  apply occurrenceAtomique in H; trivial.
  apply occurrenceConjonction in H.
  destruct H.
  left; apply IHM1; trivial.
  right; apply IHM2; trivial.
Qed.

Lemma decompositionConjonctionEquivalence :  
  forall A X (M1 M2: @Molecule A), 
                      EquivalenceMoleculaire [M1 ⊗ M2] X
                      -> exists M1' M2', 
                      X = M1' ⊗ M2' /\ EquivalenceMoleculaire [M1] M1' /\ EquivalenceMoleculaire [M2] M2'.
Proof.
Admitted.

Proposition compatibilitePresenceEquivalenceMoleculaire :
  forall A : Type,
  forall M1 M2 : @Molecule A,
  forall X : A,
    Presence M1 X -> EquivalenceMoleculaire [M1] M2 -> Presence M2 X.
Proof.
  induction M1; intros.
  - apply OccurrenceEquivPresence in H.
    destruct (aucuneOccurrenceDansUn X); trivial.
  - apply OccurrenceEquivPresence in H.
    apply occurrenceAtomique in H; trivial; subst.
    remember [atome a] as L.
    induction H0.
    -- injection HeqL; intros; subst; simpl; trivial.
    -- discriminate HeqL.
    -- injection HeqL; intros; discriminate H1.
    -- subst; destruct g; simpl in *.
      + right; apply IHEquivalenceMoleculaire2; trivial.
      + left; apply IHEquivalenceMoleculaire1; trivial.
    -- injection HeqL; intros; discriminate H1.
    -- subst; destruct n; unfold valeur in H; simpl in *.
      + injection H as H; subst.
         apply IHEquivalenceMoleculaire; trivial.
      + discriminate H.
 - simpl in H.
   destruct (decompositionConjonctionEquivalence _ M2 M1_1 M1_2); trivial.
   destruct H1. destruct H1. destruct H2.
   destruct H.
   -- apply (IHM1_1 x) in H; trivial.
      subst; simpl; left; assumption.
   -- apply (IHM1_2 x0) in H; trivial.
      subst; simpl; right; assumption.
Qed.
















