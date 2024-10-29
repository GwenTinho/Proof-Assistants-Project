(*
Previous experince:
Quentin Schroeder

I took the class about proof assistants last semester with Hugo Herbelin where we had to implement a decision proof for propositional intuintionistic logic in coq as the final project.

I had some experience before that trying to formalize some topology proofs (but failed)

And I attended the proof and computation autumn school twice, where proof assistants were discussed a lot
 *)

Require Import List.
Import ListNotations.
Inductive form : Type :=
| var ( x : nat) | bot | imp ( s t : form).
Print In.
Print incl.
Notation "s ∼> t" := (imp s t) ( at level 51, right associativity).
Notation neg s := ( imp s bot).


(* Question 1.1.a *)
Inductive ndc : list form -> form -> Prop :=
  | ndc_Ax x A : In x A -> ndc A x
  | ndc_ImpI s A t : ndc (s :: A) t -> ndc A (s ∼> t)
  | ndc_ImpE s A t : ndc A (s ∼> t) -> ndc A s -> ndc A t
  | ndc_DNE s A : ndc ((neg s) :: A) bot -> ndc A s   
.


Notation "A ⊢c s" := (ndc A s) (at level 70).


(*Question 1.1.b.1*)
Lemma ndc_id : forall A s, A ⊢c s ∼> s.
Proof.
  intros A s.
  apply ndc_ImpI.
  apply ndc_Ax.
  firstorder.
Qed.

(*Question 1.1.b.2*)
Lemma ndc_dni : forall A s, s :: A ⊢c neg (neg s).
Proof.
  intros A s.
  apply ndc_ImpI.
  apply ndc_ImpE with s; apply ndc_Ax; firstorder.
Qed.

(*Question 1.1.b.3*)
Lemma ndc_escape :  [neg (neg bot)] ⊢c bot.
Proof.
  apply ndc_ImpE with (neg bot).
  - apply ndc_Ax. firstorder.
  - apply ndc_ImpI. apply ndc_Ax. firstorder.
Qed.

(*Question 1.1.b.4*)

Lemma ndc_dne : forall A s, A ⊢c neg (neg s) ∼> s.
Proof.
  intros A s.
  apply ndc_ImpI.
  apply ndc_DNE.
  apply ndc_ImpE with (neg s);
  apply ndc_Ax; firstorder.
Qed.

(*Question 1.1.c*)

(*A helping lemma to simplify my proof*)
Lemma incl_step : forall A (x : A) l l', incl l l' -> incl (x :: l) (x :: l').
Proof.
  intros A x l l' inc.
  apply incl_cons.
  - firstorder.
  - apply incl_tl. assumption.
Qed.
  


Fact Weakc : forall A B s, A ⊢c s -> incl A B -> B ⊢c s.
Proof.
  intros A B s H.
  generalize dependent B.
  induction H as [| s A t H IH| s A t H1 IH1 H2 IH2| s A t IH]; intros B inc.
  - apply ndc_Ax. apply inc. assumption.
  - apply ndc_ImpI. apply IH. apply incl_step. assumption.
  - apply ndc_ImpE with s.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - apply ndc_DNE.
    apply IH.
    apply incl_step.
    assumption.
Qed.


(*Question 1.1.d *)

Fixpoint ground (t : form) : Prop := match t with
  | var _ => False
  | bot => True
  | imp s t => ground s /\ ground t
end.


(*Question 1.2.a*)
Inductive ndm : list form -> form -> Prop :=
  | ndm_Ax x A : In x A -> ndm A x
  | ndm_ImpI s A t : ndm (s :: A) t -> ndm A (s ∼> t)
  | ndm_ImpE s A t : ndm A (s ∼> t) -> ndm A s -> ndm A t                              
.


Notation "A ⊢m s" := (ndm A s) (at level 70).

(*Question 1.2.b*)

Lemma Weakm A B s :
A ⊢m s -> incl A B -> B ⊢m s.
Proof.
  intros H.
  generalize dependent B.
  induction H as [| s A t H IH| s A t H1 IH1 H2 IH2]; intros B inc.
  - constructor. apply inc. assumption.
  - apply ndm_ImpI. apply IH. apply incl_step. assumption.
  - apply ndm_ImpE with s.
    + apply IH1. assumption.
    + apply IH2. assumption.
Qed.

(*Question 1.2.c*)
Lemma Implication A s :
A ⊢m s -> A ⊢c s.
Proof.
  intro H.
  induction H as [| s A t H IH| s A t H1 IH1 H2 IH2].
  - apply ndc_Ax. assumption.
  - apply ndc_ImpI. assumption.
  - apply ndc_ImpE with s; assumption.
Qed.


(* Question 1.2.d*)

Fixpoint trans (t s : form) := match s with
  | var x => (var x ∼> t) ∼> t
  | bot => t
  | imp u v => trans t u ∼> trans t v
end.

(*Question 1.2.e*)




Lemma DNE_Friedman A s t :
A ⊢m (( trans t s ∼> t) ∼> t) ∼> (trans t s).
Proof.
  - apply ndm_ImpI.
    induction s.
    + simpl.
      apply ndm_ImpI.
      apply ndm_ImpE with (((var x ∼> t) ∼> t) ∼> t).
      * apply ndm_Ax. firstorder.
      * apply ndm_ImpI.
        apply ndm_ImpE with (var x ∼> t).
        -- apply ndm_Ax. firstorder.
        -- apply ndm_Ax. firstorder.
    + simpl. apply ndm_ImpE with (t ∼> t).
      * apply ndm_Ax. firstorder.
      * apply ndm_ImpI.
        apply ndm_Ax. firstorder.
   + simpl.
     apply ndm_ImpI.
     apply ndm_ImpE with ((trans t s2 ∼> t) ∼> t).
     * apply ndm_ImpI.
       apply Weakm with ((trans t s2 ∼> t) ∼> t :: A).
       -- assumption.
       -- firstorder.
    * apply ndm_ImpI.
      apply ndm_ImpE with ((trans t s1 ∼> trans t s2) ∼> t).
      -- apply ndm_Ax. firstorder.
      -- apply ndm_ImpI.
         apply ndm_ImpE with (trans t s2).
         ++ apply ndm_Ax. firstorder.
         ++ apply ndm_ImpE with (trans t s1).
            ** apply ndm_Ax. firstorder.
            ** apply ndm_Ax. firstorder.
Qed.

Corollary DNE_Friedman_Split A s t :
  (A ⊢m (trans t s ∼> t) ∼> t) -> (A ⊢m trans t s).
Proof.
  intro H.
  apply ndm_ImpE with ((trans t s ∼> t) ∼> t).
  - apply DNE_Friedman.
  - apply H.
Qed.
        
(*Question 1.2.f*)


Lemma Friedman A s t :
A ⊢c s -> map (trans t) A ⊢m trans t s.
Proof.
  intro H.
  induction H.
  - apply ndm_Ax.
    apply in_map_iff.
    exists x. auto.
  - simpl.
    apply ndm_ImpI.
    auto.
  - simpl in IHndc1.
    apply ndm_ImpE with (trans t s); assumption.
  - simpl in IHndc.
    apply DNE_Friedman_Split.
    apply ndm_ImpI.
    assumption.
Qed.
    

(*1.2.g*)

(*I tried to prove it without a lemma of this shape at first but it just wasn't general enough. This one here works nicely though*)
Lemma ground_trans_bot s:
  ground s -> forall A, A ⊢m trans bot s <-> A ⊢m s.
Proof.
  intro H.
  induction s.
  - firstorder.
  - firstorder.
  - simpl in *.
    firstorder.
    + apply ndm_ImpI.
      apply H2.
      apply ndm_ImpE with (trans bot s1).
      * apply Weakm with A; firstorder.
      * apply H3. apply ndm_Ax. firstorder.
   + apply ndm_ImpI.
     apply H2.
     apply ndm_ImpE with s1.
     * apply Weakm with A; firstorder.
     * apply H3. apply ndm_Ax. firstorder.
Qed.

Lemma ground_truths s :
ground s -> ([] ⊢m s <-> [] ⊢c s).
Proof.
  intro ground_s.  
  split.
  - apply Implication.
  - intro H.
    induction s.
    + simpl in ground_s. contradiction.
    + apply Friedman with (t := bot) in H. apply H.
    + simpl in *.
      firstorder.
      apply Friedman with (t := bot) in H.
      simpl in H.
      apply ndm_ImpI.
      rewrite <- (ground_trans_bot s2 H1).
      apply ndm_ImpE with (trans bot s1).
      * apply Weakm with []; firstorder.
      * apply (ground_trans_bot s1 H0). apply ndm_Ax. firstorder.
Qed.

(*1.2.h*)
Lemma equi_consistent : [] ⊢c bot <-> [] ⊢m bot.
Proof.
  now rewrite ground_truths.
Qed.
