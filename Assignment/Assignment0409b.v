Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import SetsClass.SetsClass.
Require Import PV.Syntax.
Import Lang_SimpleWhile.
Require Import PV.DenotationalSemantics.
Require Import PV.RelsAsDenotations.
Require Import PV.HoareLogic.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile2
       DntSem_SimpleWhile3
       DntSem_SimpleWhile3_Properties
       HoareSimpleWhile.
Local Open Scope Z.
Local Open Scope sets.
Local Open Scope string.

(************)
(** 习题：  *)
(************)

Lemma hoare_seq_valid_inv: forall P R c1 c2,
  valid {{ P }} c1 ; c2 {{ R }} ->
  exists Q: assertion,
    valid {{ P }} c1 {{ Q }} /\
    valid {{ Q }} c2 {{ R }}.
Proof.
  unfold valid.
  unfold_sem.
  intros.
  remember ⟦ c1 ⟧ as C1.
  remember ⟦ c2 ⟧ as C2.
  remember ( fun s =>  exists s1, P s1 /\ ((s1, s) ∈ C1) ) as Q1.
  exists Q1.
  split.
  + intros.
    rewrite HeqQ1.
    exists s1.
    tauto.
  + intros.
    rename s1 into s3.
    rewrite HeqQ1 in H0.
    simpl in H0.
    clear HeqQ1.
    destruct H0 as [s1 H0].
    apply (H s1 s2).
    - tauto.
    - destruct H0.
      sets_unfold.
      exists s3.
      tauto.
Qed.


(************)
(** 习题：  *)
(************)

Lemma hoare_skip_inv: forall P Q,
  provable {{ P }} skip {{ Q }} -> P |--  Q.
Proof.
  unfold derives.
  intros.
  specialize (hoare_sound {{ P }} skip {{ Q }}) as H1.
  apply H1 in H as H2.
  simpl in H2.
  unfold skip_sem in H2.
  specialize (H2 s s) as H2.
  apply H2 in H0.
  + assumption.
  + sets_unfold.
    reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

Lemma hoare_while_inv: forall P Q e c,
  provable {{ P }} while (e) do { c } {{ Q }} ->
  exists I,
    derives P I /\
    provable {{ I && [[ e ]] }} c {{ I }} /\
    Assn (I && [[! e]]) |-- Q.
Proof.
  intros.
  remember ( {{ P }} while (e) do { c } {{ Q }} ) as ht eqn:EQ.
  revert P Q EQ.
  induction H; try discriminate; intros.
  + 
    clear IHprovable.
    injection EQ as L1 L2 L3 L4.
    exists P.
    split.
    - unfold derives.
      intros.
      rewrite L1.
      assumption.
    - split.
      * rewrite <- L2, <- L3.
        assumption.
      * rewrite <- L2.
        unfold derives.
        intros.
        rewrite <- L4.
        assumption.
  + injection EQ as L1 L2 L3.
    rewrite <- L1, <- L3.
    rewrite L2 in *.
    clear P0 Q0 c0 L1 L3 L2.
    specialize (IHprovable P' Q').
    destruct IHprovable as [I [ P1 [ P2 P3 ] ] ].
    reflexivity.
    exists I.
    split.
    - unfold derives.
      intros.
      specialize (H0 s).
      specialize (P1 s).
      tauto.
    - split.
      * assumption.
      * unfold derives; intro.
        specialize (P3 s).
        specialize (H1 s).
        tauto.
Qed.
