From iris_simp_lang Require Import stack_ra.
From iris_simp_lang Require Export modality_instances.
From iris.proofmode Require Export proofmode.
From iris.base_logic Require Export iprop.
Import bi.

Section class_instances_assert_of.
  Context `{!envGS Ty Σ}.

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

  #[local] Example from_modal_up1_test P Q : ⇑ P ∗ ⇑ Q ⊢ ⇑ (P ∗ Q).
  Proof. iIntros "[? ?]". Fail iModIntro. Abort.
  Global Instance from_modal_up1 P :
    FromModal True modality_up1 (⇑ P) (⇑ P) P | 2.
  Proof. by rewrite /FromModal. Qed.
  #[local] Example from_modal_up1_test P Q : ⇑ P ∗ ⇑ Q ⊢ ⇑ (P ∗ Q).
  Proof. iIntros "[? ?]". iModIntro. iFrame. Qed.
  
  #[local] Example from_modal_down1_test P Q : ⇓ P ∗ ⇓ Q ⊢ ⇓ (P ∗ Q).
  Proof. iIntros "[? ?]". Fail iModIntro. Abort.
  Global Instance from_modal_down1 P :
    FromModal True modality_down1 (⇓ P) (⇓ P) P | 2.
  Proof. by rewrite /FromModal. Qed.
  #[local] Example from_modal_down1_test P Q : ⇓ P ∗ ⇓ Q ⊢ ⇓ (P ∗ Q).
  Proof. iIntros "[? ?]". iModIntro. iFrame. Qed.

  Global Instance from_sep_up1 P Q R :
    FromSep R P Q → FromSep (⇑ R) (⇑ P) (⇑ Q).
  Proof. rewrite /FromSep => <-. rewrite up1_sep //. Qed.
  Global Instance from_sep_down1 P Q R :
    FromSep R P Q → FromSep (⇓ R) (⇓ P) (⇓ Q).
  Proof. rewrite /FromSep => <-. rewrite down1_sep //. Qed.

  Global Instance from_and_up1 P Q R:
    FromAnd R P Q → FromAnd (⇑ R) (⇑ P) (⇑ Q).
  Proof. rewrite /FromAnd => <-. rewrite up1_and //. Qed.
  Global Instance from_and_down1 P Q R :
    FromAnd R P Q → FromAnd (⇓ R) (⇓ P) (⇓ Q).
  Proof. rewrite /FromAnd => <-. rewrite down1_and //. Qed.
  
  Global Instance from_exists_up1 {T:Type} (P:assert) (Φ:T->assert) :
    FromExist P Φ → FromExist (⇑ P) (λ x, ⇑ (Φ x))%I.
  Proof. rewrite /FromExist => <-. rewrite -up1_exist //. Qed.
  Global Instance from_exists_down1 {T:Type} (P:assert) (Φ:T->assert) :
    FromExist P Φ → FromExist (⇓ P) (λ x, ⇓ (Φ x))%I.
  Proof. rewrite /FromExist => <-. rewrite -down1_exist //. Qed.
  
  Global Instance into_wand_up1 p q (R P Q: assert) :
    IntoWand p q R P Q → IntoWand p q (⇑ R)%I (⇑ P)%I (⇑ Q)%I.
  Proof. rewrite /IntoWand /up1. intros ?.
      split => ?. f_equiv. rewrite !bi_intuitionistically_if_assert_of.
      apply wand_intro_r.
      rewrite assert_of_sep. apply assert_of_mono.
      intros v.
      rewrite -!monPred_at_intuitionistically_if -monPred_at_sep H.
      apply monPred_at_mono; last done.
      iIntros "[x y]"; by iApply "x". 
  Qed.
  Global Instance into_wand_down1 p q (R P Q: assert) :
    IntoWand p q R P Q → IntoWand p q (⇓ R)%I (⇓ P)%I (⇓ Q)%I.
  Proof. rewrite /IntoWand /down1. intros ?.
      split => ?. f_equiv. rewrite !bi_intuitionistically_if_assert_of.
      apply wand_intro_r.
      rewrite assert_of_sep. apply assert_of_mono.
      intros v.
      rewrite -!monPred_at_intuitionistically_if -monPred_at_sep H.
      apply monPred_at_mono; last done.
      iIntros "[x y]"; by iApply "x". 
  Qed.
  
  Global Instance from_wand_up1 P Q R :
    FromWand P Q R → FromWand (⇑ P) (⇑ Q) (⇑ R).
  Proof. rewrite /FromWand => <-. rewrite up1_wand //. Qed.
  Global Instance from_wand_down1 P Q R:
    FromWand P Q R → FromWand (⇓ P) (⇓ Q) (⇓ R).
  Proof. rewrite /FromWand => <-. rewrite down1_wand //. Qed.

  Global Instance into_and_up1 p P Q1 Q2 :
    IntoAnd p P Q1 Q2 → IntoAnd p (⇑ P)%I (⇑ Q1)%I (⇑ Q2)%I.   
  Proof. rewrite /IntoAnd /up1 => HP.
    rewrite assert_of_and !bi_intuitionistically_if_assert_of /=.
    apply assert_of_mono. intros v.
    rewrite -monPred_at_and -!monPred_at_intuitionistically_if HP //.
  Qed.
  Global Instance into_and_down1 p P Q1 Q2 :
    IntoAnd p P Q1 Q2 → IntoAnd p (⇓ P)%I (⇓ Q1)%I (⇓ Q2)%I. 
  Proof. rewrite /IntoAnd /down1 => HP.
    rewrite assert_of_and !bi_intuitionistically_if_assert_of /=.
    apply assert_of_mono. intros v.
    rewrite -monPred_at_and -!monPred_at_intuitionistically_if HP //.
  Qed.

  Global Instance into_sep_up1 P Q R:
    IntoSep P Q R → IntoSep (⇑ P) (⇑ Q) (⇑ R).
  Proof. rewrite /IntoSep => ->. split => i. rewrite -up1_sep //. Qed.
  Global Instance into_sep_down1 P Q R:
    IntoSep P Q R → IntoSep (⇓ P) (⇓ Q) (⇓ R).
  Proof. rewrite /IntoSep => ->. split => i. rewrite -down1_sep //. Qed.

  Global Instance from_or_up1 P Q R:
    FromOr P Q R → FromOr (⇑ P) (⇑ Q) (⇑ R).
  Proof. rewrite /FromOr => <-. monPred.unseal. done. Qed.
  Global Instance from_or_down1 P Q R:
    FromOr P Q R → FromOr (⇓ P) (⇓ Q) (⇓ R).
  Proof. rewrite /FromOr => <-. monPred.unseal. done. Qed.

  Global Instance into_or_up1 P Q R:
    IntoOr P Q R → IntoOr (⇑ P) (⇑ Q) (⇑ R).
  Proof. rewrite /IntoOr => ->. monPred.unseal. done. Qed.
  Global Instance into_or_down1 P Q R:
    IntoOr P Q R → IntoOr (⇓ P) (⇓ Q) (⇓ R).
  Proof. rewrite /IntoOr => ->. monPred.unseal. done. Qed.

  Global Instance from_exist_up1 {A} P (Φ : A → assert) :
    FromExist P Φ → FromExist (⇑ P) (λ a, ⇑ (Φ a))%I.
  Proof. rewrite /FromExist => <-. split => ?. simpl.
    rewrite monPred_at_exist /= monPred_at_exist //.
  Qed.
  Global Instance from_exist_down1 {A} P (Φ : A → assert) :
    FromExist P Φ → FromExist (⇓ P) (λ a, ⇓ (Φ a))%I.
  Proof. rewrite /FromExist => <-. split => ?. simpl.
    rewrite monPred_at_exist /= monPred_at_exist //.
  Qed.

  Global Instance into_exist_up1 {A} P (Φ : A → assert) name:
    IntoExist P Φ name → IntoExist (⇑ P) (λ a, ⇑ (Φ a))%I name.
  Proof. rewrite /IntoExist => ->. split => ?. simpl.
    rewrite monPred_at_exist /= monPred_at_exist //.
  Qed.
  Global Instance into_exist_down1 {A} P (Φ : A → assert) name:
    IntoExist P Φ name → IntoExist (⇓ P) (λ a, ⇓ (Φ a))%I name.
  Proof. rewrite /IntoExist => ->. split => ?. simpl.
    rewrite monPred_at_exist /= monPred_at_exist //.
  Qed.

  Global Instance into_forall_up1 {A} P (Φ : A → assert) :
    IntoForall P Φ → IntoForall (⇑ P) (λ a, ⇑ (Φ a))%I.
  Proof. rewrite /IntoForall=> HP. by rewrite HP up1_forall. Qed.
  Global Instance into_forall_down1 {A} P (Φ : A → assert) :
    IntoForall P Φ → IntoForall (⇓ P) (λ a, ⇓ (Φ a))%I.
  Proof. rewrite /IntoForall=> HP. by rewrite HP down1_forall. Qed.

  Global Instance from_forall_persistently_up1 {A} P (Φ : A → assert) name :
    FromForall P Φ name → FromForall (⇑ P) (λ a, ⇑ (Φ a))%I name.
  Proof. rewrite /FromForall=> <-. by rewrite up1_forall. Qed.
  Global Instance from_forall_persistently_down1 {A} P (Φ : A → assert) name :
    FromForall P Φ name → FromForall (⇓ P) (λ a, ⇓ (Φ a))%I name.
  Proof. rewrite /FromForall=> <-. by rewrite down1_forall. Qed.

  Global Instance into_pure_up1 P φ :
    IntoPure P φ → IntoPure (⇑ P) φ.
  Proof. rewrite /IntoPure => ->. rewrite -up1_objective //. Qed.
  Global Instance into_pure_down1 P φ :
    IntoPure P φ → IntoPure (⇓ P) φ.
  Proof. rewrite /IntoPure => ->. rewrite -down1_objective //. Qed.

  (* what does FromAssumption/KnownLFromAssumption etc. do? *)
  
End class_instances_up1_down1.
