(*TODO*)
From Project Require Import ex1.
Require Import List.
Import ListNotations.

(*Question 2.1.a*)

Inductive hil (A : list form) : form -> Prop :=
  | hil_Ax x: In x A -> hil A x
  | hil_ImpE s t : hil A s -> hil A (s ∼> t) -> hil A t
  | hil_Weak s t : hil A (s ∼> t ∼> s)                                              | hil_Comp s t u : hil A ((s ∼> t ∼> u) ∼> (s ∼> t) ∼> s ∼> u)
.

Notation "A ⊢H s" := (hil A s) (at level 70).


(*Question 2.1.b*)
Lemma hil_ndm A s :
  hil A s -> ndm A s.
Proof.
  intro H.
  induction H.
  - apply ndm_Ax. assumption.
  - apply ndm_ImpE with s; assumption.
  - apply ndm_ImpI. apply ndm_ImpI. apply ndm_Ax. firstorder.
  - apply ndm_ImpI.
    apply ndm_ImpI.
    apply ndm_ImpI.
    apply ndm_ImpE with t.
    + apply ndm_ImpE with s.
      * apply ndm_Ax. firstorder.
      * apply ndm_Ax. firstorder.
    + apply ndm_ImpE with s.
      * apply ndm_Ax. firstorder.
      * apply ndm_Ax. firstorder.
Qed.


(*Question 2.1.c.1*)
Example weak : forall A s t, A ⊢H s -> A ⊢H (t ∼> s).
Proof.
  intros A s t H.
  apply hil_ImpE with s.
  - assumption.
  - apply hil_Weak.
Qed.

(*Question 2.1.c.2*)
Example comp : forall A s t u, A ⊢H s ∼> t ∼> u -> A ⊢H s ∼> t -> A ⊢H s ∼> u.
Proof.
  intros A s t u H0 H1.
  apply hil_ImpE with (s ∼> t).
  - assumption.
  - apply hil_ImpE with (s ∼> t ∼> u).
    + assumption.
    + apply hil_Comp.
Qed.

(*Question 2.1.c.3*)
Example iden : forall A s, A ⊢H s ∼> s.
Proof.
  intros A s.
  apply comp with (s ∼> s).
  - apply hil_Weak.
  - apply hil_Weak.
Qed.


(*abstractions*)
Lemma hil_abs {A} : forall s t, s :: A ⊢H t -> A ⊢H s ∼> t.
Proof.
  intros s t H.
  induction H.
  - simpl in H.
    destruct H as [ <- | H].
    + apply iden.
    + apply weak.
      apply hil_Ax.
      assumption.
  - apply comp with s0; assumption.
  - apply weak. apply hil_Weak.
  - apply weak. apply hil_Comp.
Qed.


Fact ndm_hil {A s} :
  ndm A s -> hil A s.
Proof.
  intro H.
  induction H.
  - apply hil_Ax.
    assumption.
  - apply hil_abs. assumption.
  - apply hil_ImpE with s; assumption.
Qed.


    
  
  

Require Import Lia ZArith List.
Section ARS.
Context [A : Type].
Variable R : A -> A -> Prop.

Inductive SN_on : A -> Prop :=
  | SN_Step x: (forall y, R x y -> SN_on y) -> SN_on x
.

Inductive rtc : A -> A -> Prop :=
  | Refl x : rtc x x
  | Incl x y : R x y -> rtc x y
  | Trans x y z : rtc x y -> rtc y z -> rtc x z
.

Lemma SN_on_rtc x y : SN_on x -> rtc x y -> SN_on y.
Proof.
  intros Hsn Hrtc.
  induction Hrtc.
  - assumption.
  - inversion Hsn.
    subst.
    apply H0.
    apply H.
  - apply IHHrtc2. apply IHHrtc1. apply Hsn.
Qed.

Variables T V : A -> Prop.
Variable Hpres : forall x y, T x -> R x y -> T y.
Variable Hprog : forall x, T x -> (exists y, R x y) \/ V x.

Lemma SN_to_WN x :
T x ->
SN_on x ->
exists v, rtc x v /\ T v /\ V v.
Proof.
  intros Tx SNx.
  destruct (Hprog x Tx) as [[y Rxy] | Vx].
  - (*otherwise there is a next reduct, but R is strongly normalizing for at x*)
    specialize (Hpres x y Tx Rxy) as Ty.
    generalize dependent y.
    induction SNx.
    + intros y Rxy Ty.
      destruct (Hprog y Ty) as [[z Ryz] | Vy].
      * specialize (Hpres y z Ty Ryz) as Tz.
        specialize (H0 y Rxy Ty z Ryz Tz) as (v & rtczv & Tv & Vv).
        eauto 8 using Trans, Incl.
      * eauto using Incl.
  - eauto using Refl.
Qed.

End ARS.


Lemma SN_on_double_int (A B : Type) ( R1 : A -> A -> Prop) (R2 : B -> B -> Prop)
  (P : A -> B -> Prop) :
  ( forall (a : A) (b : B),
  ( forall (a' : A), R1 a a' -> SN_on R1 a') ->
  ( forall (a' : A), R1 a a' -> P a' b) ->
  ( forall (b' : B), R2 b b' -> SN_on R2 b') ->
  ( forall (b' : B), R2 b b' -> P a b') ->
  P a b
  ) -> forall (x : A) (y : B), SN_on R1 x -> SN_on R2 y -> P x y.
Proof.
  intros IH x y SNx.
  revert y.
  induction SNx.
  intros y SNy.
  induction SNy.
  apply IH; auto using SN_Step.
Qed.

Inductive term :=
| S | K | V ( n : nat) | app ( e1 e2 : term).
Coercion app : term >-> Funclass.

Implicit Type s t : form.
Implicit Type e : term.

Ltac inv H := inversion H; subst; clear H.
Section typing.
Variable A : list form.
Reserved Notation "⊢ e : s" (at level 60, e at next level).
Search nth_error.
Inductive typing : term -> form -> Prop :=
 | Var n s : nth_error A n = Some s -> typing (V n) s
 | ArrE e1 e2 s t : typing e1 (s ∼> t) -> typing e2 s -> typing (app e1 e2) t
 | Const s t : typing K (s ∼> t ∼> s)                                             | SOP s t u : typing S ((s ∼> t ∼> u) ∼> (s ∼> t) ∼> s ∼> u)
.

Notation "⊢ e : s" := ( typing e s) ( at level 60, e at next level).

Lemma hil_equiv s :
hil A s <-> exists e, ⊢ e : s.
Proof.
  split.
  - intro H.
    induction H as [s | s t Hs [e He] Ht [e0 He0]| | ].
    + apply In_iff_nth_error in H.
      destruct H as [n H].
      exists (V n). apply Var. assumption.
    + exists (app e0 e). apply ArrE with s; assumption.
    + exists K. apply Const.
    + exists S. apply SOP.
  - intros [e He].
    induction He as [n s | _ _ s t _ Hst _ Hs | | ].
    + apply nth_error_In in H. now apply hil_Ax.
    + apply ndm_hil.
      apply hil_ndm in Hst, Hs.
      now apply ndm_ImpE with s.
    + apply hil_Weak.
    + apply hil_Comp.
Qed.


Inductive red : term -> term -> Prop :=
 | redK e1 e2: red (app (app K e1) e2) e1
 | redS e1 e2 e3 : red (app (app (app S e1) e2) e3) (app (app e1 e3) (app e2 e3))
 | redAppL e1 e1' e2 : red e1 e1' -> red (app e1 e2) (app e1' e2)
 | redAppR e1 e2 e2' : red e2 e2' -> red (app e1 e2) (app e1 e2')                 .

Notation "e1 ≻ e2" := ( red e1 e2) ( at level 60).

Lemma preservation e1 e2 s :
⊢ e1 : s ->
e1 ≻ e2 ->
⊢ e2 : s.
Proof.
  revert s e2.
  induction e1; intros.
  - inversion H0.
  - inv H0.
  - inv H0.
  - inv H0.
    + inv H.
      inv H2.
      inv H1.
      assumption.
    + inv H.
      inv H2.
      inv H1.
      inv H2.
      eauto using ArrE.
    + inv H.
      specialize (IHe1_1 (s0 ∼> s) e1' H2 H4).
      eauto using ArrE.
    + inv H.
      specialize (IHe1_2 s0 e2' H5 H4).
      eauto using ArrE.
Qed.

Definition reds :=
rtc red.
Notation "e1 ≻* e2" := (reds e1 e2) ( at level 60).

Lemma app_red e1 e1' e2 :
e1 ≻* e1' ->
e1 e2 ≻* e1' e2.
Proof.
  intro H.
  revert e2.
  induction H;intro e2.
  - apply Refl.
  - apply Incl.
    apply redAppL.
    assumption.
  - apply Trans with (y e2).
    + apply IHrtc1.
    + apply IHrtc2.
Qed.

  

Lemma subject_reduction e1 e2 s :
⊢ e1 : s ->
e1 ≻* e2 ->
⊢ e2 : s.
Proof.
  intros He Hred.
  induction Hred.
  - assumption.
  - now apply preservation with x.
  - auto.
Qed.

End typing.

Notation "A ⊢ e : s" := ( typing A e s) ( at level 60, e at next level).
Notation "t1 ≻ t2" := ( red t1 t2) ( at level 60).
Notation "t1 ≻* t2" := (reds t1 t2) ( at level 60).

Definition SN (e : term) :=
SN_on red e.


Lemma SN_app e1 e2 :
SN ( e1 e2) -> SN e1.
Proof.
  constructor.
  generalize dependent e2.
  induction e1.
  - constructor.
Admitted.

Definition neutral (e : term) :=
match e with
| app K _ | K | app ( app S _) _ | S | app S _ => False
| _ => True
end.

Lemma neutral_app e1 e2 :
neutral e1 -> neutral (e1 e2).
Proof.
  intro H.
  induction e1; [easy.. | now destruct e1_1].
Qed.
    
  
Lemma progress e s :
( nil ⊢ e : s) -> (exists e', red e e') \/ ~ neutral e.
Proof.
  revert s.
  induction e; intros s H.
  - inv H.
    now right.
  - inv H.
    now right.
  - inv H. now destruct n.
  - inv H.
    specialize (IHe1 _ H2) as [[e' H3] | nneut].
    + left. exists (e' e2). apply redAppL. assumption.
    + specialize (IHe2 _ H4) as [[e'' H5] | nneut'].
      * left. exists (e1 e''). apply redAppR. assumption.
      * right. admit.
Admitted.
       
        
    
