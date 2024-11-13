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


(*Question 2.1.d*)
(*
My guess is that the induction hypthesis won't be provable anymore
 *)
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


(*Question 2.1.e*)
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


(*Question 2.2.a*)
Inductive SN_on : A -> Prop :=
  | SN_Step x: (forall y, R x y -> SN_on y) -> SN_on x
.

(*Question 2.2.b*)
Inductive rtc : A -> A -> Prop :=
  | Refl x : rtc x x
  | Incl x y : R x y -> rtc x y
  | Trans x y z : rtc x y -> rtc y z -> rtc x z
.

(*Question 2.2.c*)
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

(*Question 2.2.d*)
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

(*2.2.e*)
Lemma SN_on_double_ind (A B : Type) ( R1 : A -> A -> Prop) (R2 : B -> B -> Prop)
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

(*Question 2.3.a*)
Inductive typing : term -> form -> Prop :=
 | TV n s : nth_error A n = Some s -> typing (V n) s
 | TAPP e1 e2 s t : typing e1 (s ∼> t) -> typing e2 s -> typing (app e1 e2) t
 | TK s t : typing K (s ∼> t ∼> s)
 | TS s t u : typing S ((s ∼> t ∼> u) ∼> (s ∼> t) ∼> s ∼> u)
.

Notation "⊢ e : s" := ( typing e s) ( at level 60, e at next level).


Create HintDb hil.

Hint Resolve TAPP : hil.
Hint Resolve TK : hil.
Hint Resolve TS : hil.
Hint Resolve TV : hil.
Hint Resolve nth_error_In : hil.
Hint Resolve In_iff_nth_error : hil.
Hint Resolve hil_Weak : hil.
Hint Resolve hil_Comp : hil.
Hint Resolve ndm_hil : hil.
Hint Resolve hil_ndm : hil.
Hint Resolve ndm_ImpE : hil.
Hint Resolve hil_Ax : hil.


(*Question 2.3.b*)
Lemma hil_equiv s :
hil A s <-> exists e, ⊢ e : s.
Proof.
  split.
  - intro H.
    induction H as [s | s t Hs [e He] Ht [e0 He0]| | ]; eauto with hil.
    + apply In_iff_nth_error in H.
      destruct H as [n H].
      exists (V n). apply TV. assumption.
  - intros [e He].
    induction He as [n s | _ _ s t _ Hst _ Hs | | ]; eauto with hil.
Qed.


(*Question 2.3.c*)
Inductive red : term -> term -> Prop :=
 | redK e1 e2: red (app (app K e1) e2) e1
 | redS e1 e2 e3 : red (app (app (app S e1) e2) e3) (app (app e1 e3) (app e2 e3))
 | redAppL e1 e1' e2 : red e1 e1' -> red (app e1 e2) (app e1' e2)
 | redAppR e1 e2 e2' : red e2 e2' -> red (app e1 e2) (app e1 e2')                 .

Notation "e1 ≻ e2" := ( red e1 e2) ( at level 60).

Lemma inversion_red : forall e e', e ≻ e' -> (exists e'', e = K e' e'') \/ (exists e1 e2 e3, S e1 e2 e3 = e /\ e1 e3 (e2 e3) = e') \/ (exists e1 e1' e2, e = e1 e2 /\ e' = e1' e2) \/ (exists e1 e2 e2', e = e1 e2 /\ e' = e1 e2').
Proof.
  intros e e' R.
  inv R; firstorder eauto.
Qed.

Create HintDb reddb.
Hint Resolve inversion_red : reddb.


(*Question 2.3.d*)
Lemma preservation e1 e2 s :
⊢ e1 : s ->
e1 ≻ e2 ->
⊢ e2 : s.
Proof.
  revert s e2.
  induction e1; eauto 8 with hil reddb; intros.
  - inv H0.
  - inv H0.
  - inv H0.
  - inv H0; inv H
    + inv H2. inv H2. inv H1. assumption.
    + inv H2. inv H1. inv H2. eauto with hil.
    + eauto with hil.
    + eauto with hil.
Qed.

Definition reds :=
rtc red.
Notation "e1 ≻* e2" := (reds e1 e2) ( at level 60).

(*Question 2.3.e*)
Lemma app_red e1 e1' e2 :
e1 ≻* e1' ->
e1 e2 ≻* e1' e2.
Proof.
  intro H.
  revert e2.
  induction H; intro e2.
  - apply Refl.
  - apply Incl.
    apply redAppL.
    assumption.
  - apply Trans with (y e2).
    + apply IHrtc1.
    + apply IHrtc2.
Qed.

  
(*Question 2.3.f*)
Lemma subject_reduction e1 e2 s :
⊢ e1 : s ->
e1 ≻* e2 ->
⊢ e2 : s.
Proof.
  intros He Hred.
  induction Hred; eauto using preservation.
Qed.

End typing.

Notation "A ⊢ e : s" := ( typing A e s) ( at level 60, e at next level).
Notation "t1 ≻ t2" := ( red t1 t2) ( at level 60).
Notation "t1 ≻* t2" := (reds t1 t2) ( at level 60).

Definition SN (e : term) :=
SN_on red e.


(*idea comes from the formalization of strong normalisation for STLC that Thibault and I did for the foundations of proof systems class*)

Inductive sub_term : term -> term -> Prop :=
| Sub_app2 (t1 t2 : term) : sub_term t2 (app t1 t2)
| Sub_app1 (t1 t2 : term) : sub_term t1 (app t1 t2)
.

Lemma sn_sub_term : forall (t : term),
    SN t -> (forall t':term, sub_term t' t -> SN t').
Proof.
  intros t H. induction H.
  intros t' Hsub. inversion Hsub; subst; constructor.
  - intros u Hstep.
    eapply H0; constructor; easy.
  - intros y R.
    eapply H0; eauto using redAppL, Sub_app1.
Qed.

(*I don't know how to prove this without such a lemma, the induction hypthesis seems to weak without it*)

(*Question 2.3.g*)
Lemma SN_app e1 e2 :
SN ( e1 e2) -> SN e1.
Proof.
  intros H.
  apply sn_sub_term with (e1 e2).
  - assumption.
  - constructor.
Qed.


Definition neutral (e : term) :=
match e with
| app K _ | K | app ( app S _) _ | S | app S _ => False
| _ => True
end.

(*Question 2.3.h*)
Lemma neutral_app e1 e2 :
neutral e1 -> neutral (e1 e2).
Proof.
  intro H.
  induction e1; [easy.. | now destruct e1_1].
Qed.


(*Question 2.3.i*)
Lemma progress e s :
( nil ⊢ e : s) -> (exists e', e ≻ e') \/ ~ neutral e.
Proof.
  intro H.
  induction H.
  - rewrite nth_error_nil in H. inv H.
  - firstorder.
    + left. exists (x0 e2). apply redAppL. assumption.
    + left. exists (e1 x). apply redAppR. assumption.
    + left. exists (x e2). apply redAppL. assumption.
    + destruct e1; [firstorder .. | idtac].
      * destruct e1_1.
        -- firstorder.
        -- left.  exists e1_2. apply redK.
        -- firstorder.
        -- destruct e1_1_1; [idtac | firstorder ..].
           left. exists ((e1_1_2 e2) (e1_2 e2)). apply redS.
  - firstorder.
  - firstorder.
Qed.      
           
        
Fixpoint forces e s := match s with
| bot => SN e
| var x => SN e
| s ∼> t => forall e', forces e' s -> forces (e e') t
end.

Notation " ⊨ e : s" := (forces e s)  ( at level 60, e at next level).

(*Question 2.4.1*)
Theorem forcing_prop : forall s e, (⊨ e : s -> SN e) /\ ( ⊨ e : s -> forall e', e ≻* e' -> ⊨ e' : s) /\ (neutral e -> (forall e', e ≻ e' -> ⊨ e' : s) -> ⊨ e : s).
Proof.
  intro s.
  induction s; intro e.
  - firstorder.
    + now apply SN_on_rtc with e.
    + constructor. apply H0.
  - firstorder.
    + now apply SN_on_rtc with e.
    + constructor. apply H0.
  - split.
    + intro H.
      simpl in H.
      apply SN_app with (V 0).
      apply IHs2.
      apply H.
      apply IHs1.
      * split.
      * intros e' H0. inv H0.
    + split.
      * intros force e0 reduces e1 forces1.
        simpl in force.
        specialize (IHs2 (e e1)) as (_ & H & _).
        specialize (force e1 forces1).
        apply H.
        -- assumption.
        -- apply app_red. assumption.
      * intros N H e0 F0.
        destruct (IHs1 e0) as (H0 & _ & _).
        specialize (H0 F0).
        induction H0.
        destruct (IHs2 (e x)) as (_ & _ & H3).
        apply H3.
        -- apply neutral_app. assumption.
        -- intros e' F'.
           inv F'.
           ++ firstorder.
           ++ firstorder.
           ++ now apply H.
           ++ apply H1.
              ** assumption.
              ** destruct (IHs1 x) as (_ & H7 & _).
                 apply H7.
                 --- assumption.
                 --- apply Incl. assumption.
Qed.

        
(*Question 2.4.2*)    
Lemma K_forced : forall s t, ⊨ K : s ∼> t ∼> s.
Proof.
  intros s t e0 F0 e1 F1.
  specialize (forcing_prop s e0) as (S0 & H0 & _).
  specialize (forcing_prop t e1) as (S1 & H1 & _).
  specialize (S0 F0).
  specialize (S1 F1).
  revert F0 F1 H0 H1.
  apply SN_on_double_ind with (R1 := red) (R2 := red) (x := e0) (y := e1); try assumption.
  intros a b _ H0 _ H1 Fa Fb IHa IHb.
  apply forcing_prop.
  - split.
  - intros e' R.
    specialize (IHa Fa).
    specialize (IHb Fb).
    inv R.
    + assumption.
    + inv H4.
      * inv H5.
      * apply H0.
        -- assumption.
        -- apply IHa. now apply Incl.
        -- eauto.
        -- intros. apply IHa. apply Trans with e2'.
           ++ now apply Incl.
           ++ assumption.
        -- eauto.
    + apply H1; try assumption.
      * apply IHb. now apply Incl.
      * eauto.
      * intros. apply IHb. apply Trans with e2'.
        -- apply Incl. assumption.
        -- assumption.
Qed.



(*triple ind, i did it for SN directly instead of SN_on to make it somewhat readable*)     
Lemma SN_triple_ind
  (P : term -> term -> term -> Prop) :
  ( forall a b c,
  ( forall a', a ≻ a' -> SN a') ->
  ( forall a', a ≻ a' -> P a' b c) ->
  ( forall b', b ≻ b' -> SN b') ->
  ( forall b', b ≻ b' -> P a b' c) ->
  ( forall c', c ≻ c' -> SN c') ->
  ( forall c', c ≻ c' -> P a b c') ->
  P a b c
  ) -> forall x y z, SN x -> SN y -> SN z -> P x y z.
Proof.
  intros IH x y z SNx.
  revert y z.
  induction SNx.
  intros y z SNy.
  generalize dependent z.
  induction SNy.
  intros z SNz.
  induction SNz.
  apply IH; try auto.
  - intros.
    apply H0; [assumption | constructor; auto | constructor; auto].
  - intros.
    apply H2; [easy | constructor; auto ].
Qed.

(*Question 2.3.3*)
Lemma S_forced : forall s t u, ⊨ S : (s ∼> t ∼> u) ∼> (s ∼> t) ∼> s ∼> u.
Proof.
  intros s t u e0 F0 e1 F1 e2 F2.
  specialize (forcing_prop (s ∼> t ∼> u) e0) as (S0 & H0 & _).
  specialize (S0 F0).
  specialize (forcing_prop (s ∼> t) e1) as (S1 & H1 & _).
  specialize (S1 F1).
  specialize (forcing_prop s e2) as (S2 & H2 & _).
  specialize (S2 F2).
  revert F0 F1 F2 H0 H1 H2. 
  apply SN_triple_ind with (x := e0) (y := e1) (z := e2); try assumption.
  intros a b c _ H0 _ H1 _ H2 Fa Fb Fc IHa IHb IHc.
  apply forcing_prop.
  - split.
  - specialize (IHa Fa).
    specialize (IHb Fb).
    specialize (IHc Fc).
    intros d R.
    inv R.
    + simpl in Fa. apply Fa.
      * assumption.
      * simpl in Fb. apply Fb. assumption.
    + inv H5.
      * inv H6.
        -- inv H5.
        -- apply H0; eauto using Incl.
           ++ apply IHa. now apply Incl.
           ++ intros Fe2' e' Re'.
              apply IHa. apply Trans with e2'.
              ** now apply Incl.
              ** assumption.
      * apply H1; eauto.
        -- apply IHb. now apply Incl.
        -- intros Fe2' e' Re'.
           apply IHb. apply Trans with e2'.
           ++ now apply Incl.
           ++ assumption.
    + apply H2; eauto.
      * apply IHc. now apply Incl.
      * intros Fe2' e' Re'.
        apply IHc. apply Trans with e2'.
        -- now apply Incl.
        -- assumption.
Qed.

(*Question 2.3.4*)
Theorem V_forced : forall A s e, (forall t n, nth_error A n = Some t -> ⊨ V n : t) -> A ⊢ e : s -> ⊨ e : s.
Proof.
  intros A s e H types.
  induction types.
  - now apply H.
  - exact (IHtypes1 e2 IHtypes2).
  - apply K_forced.
  - apply S_forced.
Qed.

(*Question 2.3.5*)
Lemma well_typed_is_sn : forall s e, [] ⊢ e : s -> SN e.
Proof.
  intros s e H.
  specialize (forcing_prop s e) as [H0 _].
  apply H0.
  clear H0.
  generalize dependent s.
  induction e; intros s H.
  - inv H.
    apply S_forced.
  - inv H.
    apply K_forced.
  - inv H.
    apply V_forced with nil; rewrite nth_error_nil in H1; inv H1.
  - inv H.
    apply IHe1 in H2.
    apply IHe2 in H4.
    apply (H2 e2 H4).
Qed.

(*Question 2.3.6*)
Lemma well_typed_is_wn :
  forall s e, [] ⊢ e : s -> exists e', e ≻* e' /\ [] ⊢ e' : s /\ ~ neutral e'.
Proof.
  intros s e H.
  apply SN_to_WN; eauto using preservation, progress.
  now apply well_typed_is_sn with s. 
Qed.

(*Question 2.6.a*)
Lemma noterm e :
~ [] ⊢ e : bot.
Proof.
  intro H.
  specialize (well_typed_is_wn bot e H) as (e' & H1 & H2 & H3).
  destruct e'.
  - inv H2.
  - inv H2.
  - inv H2.
    rewrite nth_error_nil in H4. inv H4.
  - inv H2.
    destruct e'1.
    + inv H5.
    + inv H5.
    + inv H5.
      rewrite nth_error_nil in H2. inv H2.
    + destruct e'1_1.
      * inv H5.
        inv H4.
      * firstorder.
      * inv H5.
        inv H4.
        rewrite nth_error_nil in H2. inv H2.
      * firstorder.
Qed.

(*Question 2.6.b*)
Corollary nd_consistent :
~ [] ⊢m bot.
Proof.
  intro H.
  apply ndm_hil in H.
  apply hil_equiv in H.
  destruct H as [e H].
  apply noterm in H.
  assumption.
Qed.

(*Question 2.6.c*)
Corollary ndc_consistent :
~ [] ⊢c bot.
Proof.
  rewrite equi_consistent.
  apply nd_consistent.
Qed.
    
  
  
  
  
  
