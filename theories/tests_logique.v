Require Export reactions_transformations reactions_transformations_meta.

Import ListNotations.

(* TODO: All examples *)

Inductive At :=
| A : nat -> At
| B : nat -> At
| C : nat -> nat -> At.

(* (A 1) ⊗ ((A 1) -o (B 1)) ⊢ (B 1) *)
Proposition Test1 :
  Transformation [True ? (atome (A 1)) -o (atome (B 1))]
           (atome (A 1))
           (atome (B 1)).
Proof.
  eapply (reactionTransformation 0 True); simpl; trivial.
  apply identiteTransformation; trivial.
  apply identiteAtome.
  apply (neutreTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply identiteAtome.
Qed.

(* (A 1) ⊗ !(∀x, (A x) -o (B x)) ⊢ (B 1) *)
Proposition Test2 :
  Transformation [∀1 (fun x => ((x = 1) ? (atome (A x)) -o (atome (B x))))]
           (atome (A 1))
           (atome (B 1)).
Proof.
  eapply (instanciationValeur 0 1); simpl; trivial; simpl.
  eapply (reactionTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply identiteAtome.
  apply (neutreTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply identiteAtome.
Qed.

(* (A 1) ⊗ (B 3) ⊗ (∀ X, ∀x, ((A x) ⊗ X) -o ((B x) ⊗ X)) ⊢ (B 1) ⊗ (B 3) *)
Proposition Test3 :
  Transformation [∀2 fun X => ∀1 fun x => ((Absence X (A 3)) ? ((atome (A x)) ⊗ X) -o ((atome (B x)) ⊗ X))]
            ((atome (A 1)) ⊗ (atome (B 3)))            
            ((atome (B 1)) ⊗ (atome (B 3))).
Proof.
  eapply (instanciationMolecule 0 (atome (B 3))); simpl; trivial; simpl.
  eapply (instanciationValeur 0 1); simpl; trivial; simpl.
  eapply (reactionTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply conjonctionMultiplicativeGauche.
  eapply (conjonctionMultiplicativeDroite 1); simpl; apply identiteAtome.
  unfold not; intro; discriminate H.
  apply (neutreTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply conjonctionMultiplicativeGauche.
  eapply (conjonctionMultiplicativeDroite 1); simpl; apply identiteAtome.
Qed.

(* 
- (A 1) ⊗ (A 1) ⊗ !((A 1) -o (B 1)) ⊢ (B 1) ⊗ (B 1) 
- comme une molécule est insécable lors d'une transition (voir la règle de coupure), 
il est nécessaire de récrire ainsi le séquent :
- (A 1) ⊗ (A 1) ⊗ !(∀2 X, (A 1) ⊗ X -o (B 1) ⊗ X) ⊢ (B 1) ⊗ (B 1) 
*)

Proposition Test4 :
  Transformation [∀2 fun X => (True ? ((atome (A 1)) ⊗ X) -o ((atome (B 1)) ⊗ X));
                         ∀2 fun X => (True ? ((atome (A 1)) ⊗ X) -o ((atome (B 1)) ⊗ X))]
             ((atome (A 1)) ⊗ (atome (A 1)))
             ((atome (B 1)) ⊗ (atome (B 1))).
Proof.
  eapply (instanciationMolecule 0 (atome (A 1))); simpl; trivial; simpl.
  eapply (reactionTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply conjonctionMultiplicativeGauche.
  eapply (conjonctionMultiplicativeDroite 1); simpl; apply identiteAtome.
  apply (neutreTransformation 0); simpl; trivial.
  eapply (instanciationMolecule 0 (atome (B 1))); simpl; trivial; simpl.
  eapply (reactionTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply conjonctionMultiplicativeGauche.
  eapply (premierGauche 1); unfold valeur; simpl; trivial.
  eapply (conjonctionMultiplicativeDroite 1); simpl; apply identiteAtome.
  apply (neutreTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply conjonctionMultiplicativeGauche.
  eapply (conjonctionMultiplicativeDroite 1); simpl; apply identiteAtome.
Qed.

(* 
- (A 1) ⊗ (A 2) 
  ⊗ (∀2 X, ((A 1) ⊗ X) -o ((B 1) ⊗ X)) 
  ⊗ (∀2 X, ((A 2) ⊗ X) -o ((B 2) ⊗ X)) 
⊢ (B 1) ⊗ (B 2) 

*)

Proposition Test5 :
  Transformation
    [∀2 fun X => (True ? ((atome (A 2)) ⊗ X) -o ((atome (B 2)) ⊗ X)); 
    ∀2 fun X => ((Absence X (A 2)) ? ((atome (A 1)) ⊗ X) -o ((atome (B 1)) ⊗ X))
    ]
             ((atome (A 1)) ⊗ (atome (A 2)))
             ((atome (B 1)) ⊗ (atome (B 2))).
Proof.
  eapply (instanciationMolecule 0 (atome (A 1))); simpl; trivial; simpl.
  eapply (reactionTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply conjonctionMultiplicativeGauche.
  eapply (premierGauche 1); unfold valeur; simpl; trivial.
  eapply (conjonctionMultiplicativeDroite 1); simpl; apply identiteAtome.
  apply (neutreTransformation 0); simpl; trivial.
  eapply (instanciationMolecule 0 (atome (B 2))); simpl; trivial; simpl.
  eapply (reactionTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply conjonctionMultiplicativeGauche.
  eapply (premierGauche 1); unfold valeur; simpl; trivial.
  eapply (conjonctionMultiplicativeDroite 1); simpl; apply identiteAtome.
  unfold not; intro; discriminate H.
  apply (neutreTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  apply conjonctionMultiplicativeGauche.
  eapply (conjonctionMultiplicativeDroite 1); simpl; apply identiteAtome.
Qed.

(* (A 1) 
   ⊗ !(∀ X, ∀x, (Absence X (B x)) ? ((A x) ⊗ X) -o ((A x) ⊗ (B x) ⊗ X)) 
   ⊢ (A 1) ⊗ (B 1) final 
*)
Proposition Test6 :
  Transformation
    [∀2 fun X => (∀1 fun x => ((Absence X (B x)) ? ((atome (A x)) ⊗ X) -o ((atome (A x)) ⊗ (atome (B x)) ⊗ X)))]
    (atome (A 1))
    ((atome (A 1)) ⊗ (atome (B 1))).
Proof.
  eapply (instanciationMolecule 0 un); simpl; trivial; simpl.
  eapply (instanciationValeur 0 1); simpl; trivial; simpl.
  eapply (reactionTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  eapply (conjonctionMultiplicativeDroite 1); simpl; constructor.
  apply (neutreTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial.
  do 2 apply conjonctionMultiplicativeGauche.
  apply (conjonctionMultiplicativeDroite 1); simpl; try constructor.
  eapply (premierGauche 1); unfold valeur; simpl; trivial.
  repeat constructor.
Qed.

(* (C 1 2) ⊗ !(∀x y, (C x y) -o (C y x)) ⊢ (C 2 1) *)
Proposition Test7 :
  Transformation [∀1 fun x => ∀1 fun y => (True ? (atome (C x y)) -o (atome (C y x)))]
           (atome (C 1 2))
           (atome (C 2 1)).
Proof.
  eapply (instanciationValeur 0 1); simpl; trivial; simpl.
  eapply (instanciationValeur 0 2); simpl; trivial; simpl.
  eapply (reactionTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial; constructor.
  apply (neutreTransformation 0); simpl; trivial.
  apply identiteTransformation; trivial; constructor.
Qed.
