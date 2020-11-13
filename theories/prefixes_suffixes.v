Require Export preambule_nat preambule_liste.

Import ListNotations.

(*
 * Préambule.
 * P1. listes
 * Théorie catégorique des préfixes et des suffixes
 * Elle vise à définir les [pré|suf]fixes d'une concaténation facilement.
 * Préfixe, suffixe : deux transformations naturelles du foncteur Liste vers le
 * foncteur monadique (Curseur -> Liste _ * Curseur) où Curseur 
 * représente l'ensemble des intervalles [0, n[ ou [n, +infini[ suivant les cas. 
 *)

(* Préambule - sur les monades *)

Definition extensionMonadiqueFonctionUnaire{A B : Type}
           (M : Type -> Type)
           (unite : forall {X}, X -> M X)
           (liaison : forall {X Y}, M X -> (X -> M Y) -> M Y)
           (f : A -> B)
  : M A -> M B
  := fun m  =>
       liaison
         m
         (fun a => unite (f a) ).

Definition extensionMonadiqueFonctionBinaire{A B C : Type}
           (M : Type -> Type)
           (unite : forall {X}, X -> M X)
           (liaison : forall {X Y}, M X -> (X -> M Y) -> M Y)
           (f : A -> B -> C)
  : M A -> M B -> M C
  := fun m1 m2 =>
       liaison
         m1
         (fun a =>
           liaison
             m2
             (fun b => unite (f a b) )).

(* Deux monades : Liste et Reglage *) 

(* Liste ( := list) est un foncteur. *)

Definition applicationListe{A B : Type} : (* map *)
  (A -> B) -> list A -> list B.
  fix REC 2.
  intros f l.
  destruct l as [ | tl rl].
  {
    exact [].
  }
  {
    exact (f tl :: REC f rl).
  }
Defined.

(* Liste est une monade. *)

Definition uniteListe{A : Type} (* unit *)
  : A -> list A
  := fun a => [a].

Definition liaisonListe{A B : Type} (* bind *)
  : list A -> (A -> list B) -> list B.
  fix REC 1.
  intros l calculParam.
  destruct l as [ | tl rl].
  {
    exact [].
  }
  {
    exact (calculParam tl ++ REC rl calculParam).
  }
Defined.

(* La monade d'état *)

Definition Etat(E T : Type) 
  : Type
  := (E -> T * E). (* E état, T observé *)

(* Pour tout E, (Etat E) est un foncteur. TODO propriétés *)

Definition applicationEtat{E A B : Type} : (* map *)
  (A -> B) -> Etat E A -> Etat E B.
  intros f ta.
  intro e.
  exact (f (fst (ta e)), snd (ta e)).
Defined.

(* Etat est une monade. TODO propriétés *)

Definition uniteEtat{E A : Type} (* unit *)
  : A -> Etat E A.
  intros a e.
  exact (a, e).
Defined.

Print uniteEtat.

Definition liaisonEtat{E A B : Type} (* bind *)
  : Etat E A -> (A -> Etat E B) -> Etat E B.
  intros ta calculParam e.
  exact(calculParam (fst (ta e)) (snd (ta e))).
Defined.

(* Le réglage, instance de l'état *)

Definition Reglage(V T : Type)  (* Tuner *)
  : Type
  := Etat V (list T). (* V variant, liste observée de T  *)

(* Pour tout V, (Reglage V) est un foncteur. TODO propriétés *)

Definition applicationReglage{V A B : Type} : (* map *)
  (A -> B) -> Reglage V A -> Reglage V B.
  intros f ra.
  intro v.
  exact (applicationListe f (fst (ra v)), snd (ra v)).
Defined.

Inductive Curseur (* Cursor *)
  : Type
  := 
  | VAL : forall n : nat, Curseur.

Definition valeurCurseur(c : Curseur) : nat.
  destruct c as [n].
  exact n.
Defined.  

Inductive Fenetre (* Window *)
  : Type
  :=
  | PLAGE : forall n d : nat, Fenetre.

Definition plageFenetre(f : Fenetre) : nat * nat.
  destruct f as [n d].
  exact (n, d).
Defined.  


(* Prefixe est une transformation naturelle du foncteur Liste vers le foncteur (Reglage Curseur). *)
(* TODO propriétés *)
Definition prefixeRC{T : Type}
  : list T -> Reglage Curseur T.
  fix REC 1.
  intros l c.
  destruct l as [ | tl rl].
  {
    exact ([], c).
  }
  {
    destruct c as [[ | pn]].
    {
      exact([], VAL 0).
    }
    {
      exact (tl :: fst (REC rl (VAL pn)), snd (REC rl (VAL pn))).
    }
  }
Defined.

(* Suffixe est une transformation naturelle du foncteur Liste vers le foncteur ReglageCurseur. *)
(* TODO propriétés *)

Definition suffixeRC{T : Type}
  : list T -> Reglage Curseur T.
  fix REC 1.
  intros l c.
  destruct l as [ | tl rl].
  {
    exact ([], c).
  }
  {
    destruct c as [[ | pn]].
    {
      exact(tl :: rl, VAL 0).
    }
    {
      exact (REC rl (VAL pn)).
    }
  }
Defined.

Definition suffixe{T : Type}
  : nat -> list T -> list T.
  fix REC 2.
  intros n l.
  destruct l as [ | tl rl].
  {
    exact [].
  }
  {
    destruct n as [ | pn].
    {
      exact(tl :: rl).
    }
    {
      exact (REC pn rl).
    }
  }
Defined.


Definition prefixe{T : Type}
  : nat -> list T -> list T.
  fix REC 2.
  intros n l.
  destruct l as [ | tl rl].
  {
    exact [].
  }
  {
    destruct n as [ | pn].
    {
      exact [].
    }
    {
      exact (tl :: (REC pn rl)).
    }
  }
Defined.


(* Sous-liste *)

Definition sousListeRF{T : Type}
  : list T -> Reglage Fenetre T.
  fix REC 1.
  intros l v.
  destruct l as [ | tl rl].
  {
    exact ([], v).
  }
  {
    destruct v as [n d].
    destruct n as [ | pn].
    {
      destruct d as [ | pd].
      {
        exact ([], PLAGE 0 0).
      }
      {
        exact (tl :: (fst (REC rl (PLAGE 0 pd))), snd (REC rl (PLAGE 0 pd))).
      }        
    }
    {
      exact (REC rl (PLAGE pn d)).
    }
  }
Defined.

(* sous liste n d l := l[n:n+d[ *)
Definition sousListe{T : Type}
  : nat -> nat -> list T -> list T.
  fix REC 3.
  intros n d l.
  destruct l as [ | tl rl].
  {
    exact [].
  }
  {
    destruct n as [ | pn].
    {
      destruct d as [ | pd].
      {
        exact [].
      }
      {
        exact (tl :: (REC 0 pd rl)).
      }        
    }
    {
      exact (REC pn d rl).
    }
  }
Defined.

Definition valeur{T : Type}(n : nat)(l : list T)
  : list T
  := sousListe n 1 l.

(* concaténation monadique *)

Definition concatenationMonadiqueR{V T : Type}
  : Reglage V T -> Reglage V T -> Reglage V T
  := extensionMonadiqueFonctionBinaire
       (@Etat V)
       (@uniteEtat V)
       (@liaisonEtat V)
       (@app T).

(* Voie directe plus simple *)
Definition concatenationR{V T : Type}
  : Reglage V T -> Reglage V T -> Reglage V T.
  intros r1 r2.
  intro v.
  exact (
      fst (r1 v) ++ fst (r2 (snd(r1 v)))
      ,
      snd (r2 (snd(r1 v)))
      ).
Defined.

