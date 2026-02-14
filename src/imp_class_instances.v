From iris_simp_lang Require Import stack_ra .
From iris_simp_lang Require Export modality_instances.
From iris.proofmode Require Export proofmode.
From iris.base_logic Require Export iprop.
Import bi.

Section class_instances_assert_of.
  Context `{!envGS Ty Σ}.

  #[local] Example from_modal_up1_test P Q : ⇑ P ∗ ⇑ Q ⊢ ⇑ (P ∗ Q).
  Proof. iIntros "[? ?]". Fail iModIntro. Abort.

  Global Instance from_modal_up1 P :
    FromModal True modality_up1 (⇑ P) (⇑ P) P | 2.
  Proof. by rewrite /FromModal. Qed.

  #[local] Example from_modal_up1_test P Q : ⇑ P ∗ ⇑ Q ⊢ ⇑ (P ∗ Q).
  Proof. iIntros "[? ?]". iModIntro. iFrame. Qed.

  Lemma bi_intuitionistically_if_assert_of p (P : nat → (iPropI Σ)) :
    □?p (assert_of (λ v, P v)) ⊣⊢ assert_of (λ v, □?p (P v)).
  Proof. split => ?. rewrite monPred_at_intuitionistically_if //. Qed.
  
  Lemma assert_of_sep (P Q : nat → (iPropI Σ)) :
    assert_of (λ v, P v) ∗ assert_of (λ v, Q v) ⊣⊢ assert_of (λ v, P v ∗ Q v).
  Proof. split => ?. rewrite monPred_at_sep //. Qed.
  
  Lemma assert_of_mono P Q :
    (∀ v, P v ⊢ Q v) → assert_of (λ v, P v) ⊢ assert_of (λ v, Q v).
  Proof. split => ?. simpl. rewrite H //. Qed.

  Lemma assert_of_and (P Q : nat → (iPropI Σ)) :
    assert_of (λ v, P v) ∧ assert_of (λ v, Q v) ⊣⊢ assert_of (λ v, P v ∧ Q v).
  Proof. split => ?. rewrite monPred_at_and //. Qed.

  Global Instance maybe_combine_sep_as_assert_of : forall Q1 Q2 P progress,
    MaybeCombineSepAs Q1 Q2 P progress →
    MaybeCombineSepAs (assert_of (λ n, Q1)) (assert_of (λ n, Q2)) (assert_of (λ n, P)) progress | 1.
  Proof. rewrite /MaybeCombineSepAs. intros. split => ?. rewrite monPred_at_sep //. Qed.

  Global Instance combine_sep_gives_assert_of : forall Q1 Q2 P,
    CombineSepGives Q1 Q2 P →
    CombineSepGives (assert_of (λ n, Q1)) (assert_of (λ n, Q2)) (assert_of (λ n, P)).
  Proof. rewrite /CombineSepGives. intros. split => ?.
    rewrite monPred_at_sep monPred_at_persistently //.
  Qed.

  Lemma combine_sep_assert_of_test P Q :
    ⊢ (assert_of (λ n, P)) -∗ (assert_of (λ n, Q)) -∗ assert_of (λ n, P ∗ Q).
  Proof. iIntros "x y". by iCombine "x y" as "x". Qed.

End class_instances_assert_of.


Section class_instances_up1_down1.
  Context `{!envGS Ty Σ}.
  
  Global Instance from_sep_up1 : forall P Q, FromSep (⇑ (P ∗ Q))%I (⇑ P) (⇑ Q).
  Proof. intros; rewrite /FromSep -up1_sep //. Qed.
  
  Global Instance from_and_up1 : forall P Q, FromAnd (⇑ (P ∧ Q))%I (⇑ P) (⇑ Q).
  Proof. intros; rewrite /FromAnd -up1_and //. Qed.
  
  Global Instance from_exists_up1 : forall {T:Type} (P: T → assert),
    FromExist (∃ x, ⇑ (P x))%I (λ x, ⇑ (P x))%I.
  Proof. intros; rewrite /FromExist -up1_exist //. Qed.
  
  Global Instance into_wand_up1 p q (R P Q: assert) : IntoWand p q R P Q → IntoWand p q (⇑ R)%I (⇑ P)%I (⇑ Q)%I.
  Proof. rewrite /IntoWand /up1. intros ?.
      split => ?. f_equiv. rewrite !bi_intuitionistically_if_assert_of.
      apply wand_intro_r.
      rewrite assert_of_sep. apply assert_of_mono.
      intros v.
      rewrite -!monPred_at_intuitionistically_if -monPred_at_sep H.
      apply monPred_at_mono; last done.
      iIntros "[x y]"; by iApply "x". 
  Qed.
  
  Global Instance into_and_up1 p P Q1 Q2 :
    IntoAnd p P Q1 Q2 → IntoAnd p (⇑ P)%I (⇑ Q1)%I (⇑ Q2)%I. 
  Proof. rewrite /IntoAnd /up1 => HP.
    rewrite assert_of_and !bi_intuitionistically_if_assert_of /=.
    apply assert_of_mono. intros v.
    rewrite -monPred_at_and -!monPred_at_intuitionistically_if HP //.
  Qed.

  (* what does FromAssumption/KnownLFromAssumption etc. do? *)

  Global Instance from_sep_down1 : forall P Q, FromSep (down1 (P ∗ Q))%I (down1 P) (down1 Q).
  Proof. intros; rewrite /FromSep -down1_sep //. Qed.
  
  Global Instance from_and_down1 : forall P Q, FromAnd (down1 (P ∧ Q))%I (down1 P) (down1 Q).
  Proof. intros; rewrite /FromAnd -down1_and //. Qed.
  
  Global Instance from_exists_down1 : forall {T:Type} (P: T → assert),
    FromExist (∃ x, down1 (P x))%I (λ x, down1 (P x)).
  Proof. intros; rewrite /FromExist -down1_exist //. Qed.
  
End class_instances_up1_down1.
