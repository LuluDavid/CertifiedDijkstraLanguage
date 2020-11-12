Require Import dijkstra tactics dijkstra_compute.

Import Pondéré.

(** GENERATED WITH CertifiedDjikstraLanguage, DO NOT EDIT *)

Definition Graph := g 1 2 4 ⊗ g 1 4 1 ⊗ g 1 5 2 ⊗ g 4 5 2 ⊗ g 4 6 3 ⊗ g 5 6 1 ⊗ g 5 3 0 ⊗ g 3 2 3 ⊗ g 4 2 4.

Definition Root := 1.

(** TODO: The two following functions should be hidden somehow *)

(** Dijkstra's final table *)
Definition FinalTableGraph := snd (Djikstra Root Graph).

(** Dijkstra's arc generation tactic*)
Ltac generationTacticGraph := addArcs (fst(Djikstra Root Graph)) (MoleculeToTriplets FinalTableGraph).

(** Simple transformation test from Graph to FinalTableGraph *)
Theorem RecouvrementGraph:
Transformation règles (Graph ⊗ t Root Root 0)
					  (Graph ⊗ FinalTableGraph).
Proof.
  (** Unfold the elements *)
	unfold Graph.
	unfold Root.
  	remember FinalTableGraph as H.
	cbv in HeqH; subst.

	(** Generate the graph *)
	generationTacticGraph.
	
	(** Check the final constraints *)
	ChoisirNeutrePartout.
	ConclureCandidat1.
	ConclureCandidat2.
Qed.

(** The tests should be in a small CI *)

