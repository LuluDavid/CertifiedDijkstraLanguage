Require Import Bool Arith List Bool.
Import ListNotations.

(** Generic boolean equalities (via Coq Classes) *)

Delimit Scope eqb_scope with eqb.
Local Open Scope eqb_scope.

Class Eqb (A : Type) := eqb : A -> A -> bool.
Infix "=?" := eqb : eqb_scope.
Arguments eqb {A} {_} !_ !_.

Class EqbSpec A `{Eqb A} :=
 eqbspec : forall x y:A, reflect (x=y) (x =? y).

Hint Extern 10 => case eqbspec : eqb.

Instance eqb_inst_nat : Eqb nat := Nat.eqb.
Instance eqbspec_nat : EqbSpec nat := Nat.eqb_spec.

Arguments eqb_inst_nat !_ !_.

Lemma eqb_refl {A} `{EqbSpec A} (x:A) : (x =? x) = true.
Proof.
 now case eqbspec.
Qed.

Lemma eqb_eq {A} `{EqbSpec A} (x y:A) : (x =? y) = true <-> x = y.
Proof.
 now case eqbspec.
Qed.

Lemma eqb_neq {A} `{EqbSpec A} (x y:A) : (x =? y) = false <-> x <> y.
Proof.
 now case eqbspec.
Qed.

Lemma eqb_sym {A} `{EqbSpec A} (x y:A) : (x =? y) = (y =? x).
Proof.
 case (eqbspec y x); intros.
 - apply eqb_eq. auto.
 - apply eqb_neq. auto.
Qed.

Ltac cons := constructor; congruence.

(** for Couples *)

Instance eqb_inst_couples {A}`{Eqb A} {B}`{Eqb B} : Eqb (A*B) := 
  fun '(x1,x2) '(y1,y2) => (x1 =? y1) && (x2 =? y2).

Instance eqbspec_couples {A}`{EqbSpec A} {B}`{EqbSpec B}  : EqbSpec (A*B).
Proof.
  red.
  intros.
  simpl. destruct x; destruct y.
  case (eqbspec a a0); case (eqbspec b b0); intros H3 H4; subst; unfold eqb; simpl.
  do 2 rewrite eqb_refl; simpl; cons.
  apply eqb_neq in H3; rewrite H3; rewrite andb_false_r; constructor.
  unfold not; intros; injection H4 as H4; subst; apply eqb_neq in H3; destruct H3; trivial.
  apply eqb_neq in H4; rewrite H4; rewrite andb_false_l; constructor.
  unfold not; intros; injection H3 as H3; subst; apply eqb_neq in H4; destruct H4; trivial.
  apply eqb_neq in H3; rewrite H3; rewrite andb_false_r; constructor.
  unfold not; intros; injection H5 as H5; subst; apply eqb_neq in H3; destruct H3; trivial.
Defined.



(** for Lists *)

Definition list_forallb {A B} (f: A -> B -> bool) :=
 fix forallb2 l1 l2 :=
 match l1, l2 with
 | [], [] => true
 | x1::l1, x2::l2 => f x1 x2 && forallb2 l1 l2
 | _, _ => false
 end.

Instance eqb_inst_list {A}`{Eqb A} : Eqb (list A) := list_forallb eqb.

Instance eqbspec_list {A}`{EqbSpec A} : EqbSpec (list A).
Proof.
 red.
 induction x; destruct y; simpl; try cons.
 cbn.
 case eqbspec; [ intros <- | cons ].
 case IHx; cons.
Defined.

Fixpoint indexOf{A:Type}`{Eqb A} x l :=
  match l with
  | []     => None
  | e::l' => if (e =? x) then Some 0 else option_map S (indexOf x l')
  end.

(* Nécessité de faire un replace en retirant x et en rajoutant y avec push pour certaines règles *)

Fixpoint list_mem {A}`{Eqb A} (x:A) (l:list A) :=
  match l with
  | [] => false
  | y::l => (x =? y) || list_mem x l
  end.

Fixpoint intersection {A}`{Eqb A} (l1 l2:list A) :=
  match l1 with
  |x::l1' => let res := (intersection l1' l2) in
                (if list_mem x l2 then x :: res else res)
  |[]     => []
  end.

Fixpoint remove{A:Type}`{Eqb A} x (l:@list A) :=
  match l with
  | []     => []
  | e::l' => if (e =? x) then l' else e::(remove x l')
   end.

Definition replace{A:Type}`{Eqb A} x y (l:@list A) (push: A -> @list A -> @list A) := push y (remove x l).