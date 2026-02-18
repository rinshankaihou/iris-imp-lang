From iris_imp_lang Require Import stack_ra.
From iris.proofmode Require Export classes.
Import bi.

(* set up modality mixin for up1 and down1.
  See the MoSel paper for the meaning of the mixin: https://iris-project.org/pdfs/2018-icfp-mosel-final.pdf *)

Section modalities.
  Context `{!envGS Ty Σ}.

  Class IntoUp1 (P Q: assert) :=
    into_up1 : P ⊢ up1 Q.
  Global Arguments IntoUp1 _%I _%I.
  Global Arguments into_up1 _%I _%I {_}.
  Global Hint Mode IntoUp1 ! -  : typeclass_instances.
  
  Class IntoDown1 (P Q: assert) :=
    into_down1 : P ⊢ down1 Q.
  Global Arguments IntoDown1 _%I _%I.
  Global Arguments into_down1 _%I _%I {_}.
  Global Hint Mode IntoDown1 ! -  : typeclass_instances.

  Global Instance into_up1_up1 P :
    IntoUp1 (⇑ P) P | 0.
  Proof. done. Qed.

  Global Instance into_up1_objective P :
    Objective P → IntoUp1 P P | 2.
  Proof.
    rewrite /IntoUp1  => ?.
    rewrite -up1_objective //.
  Qed.

  (* turns
      P
      ----------------∗
      ⇑ Q
    into
      ⇓ P
      ----------------∗
      Q
  *)
  Global Instance into_up1_from_down P :
    IntoUp1 P (⇓ P) | 100.
  Proof.
    rewrite /IntoUp1 up1_down1 //.
  Qed.

  Global Instance into_down1_down1 P :
    IntoDown1 (⇓ P) P | 0.
  Proof. rewrite /IntoDown1 //. Qed.

  Global Instance into_down1_objective P :
    Objective P → IntoDown1 P P | 2.
  Proof.
    rewrite /IntoDown1  => ?.
    rewrite -down1_objective //.
  Qed.

  Lemma modality_up1_mixin :
    modality_mixin up1 (MIEnvTransform IntoUp1) (MIEnvTransform IntoUp1).
  Proof.
    split; simpl;
    eauto using equiv_entails_1_2, up1_objective, up1_and, up1_mono, up1_sep, up1_intuitionistically with typeclass_instances.
    (* FIXME get rid of the following? *)
    - split; iIntros. + rewrite H up1_intuitionistically //. + rewrite up1_and //.
    - rewrite -up1_objective //.
    - intros. rewrite up1_sep //.
  Qed.

  Lemma modality_down1_mixin :
    modality_mixin down1 (MIEnvTransform IntoDown1) (MIEnvTransform IntoDown1).
  Proof.
    split; simpl;
    eauto using equiv_entails_1_2, down1_objective, down1_and, down1_mono, down1_sep, down1_intuitionistically with typeclass_instances.
    - split; iIntros. + rewrite H down1_intuitionistically //. + rewrite down1_and //.
    - rewrite -down1_objective //.
    - intros. rewrite down1_sep //.
  Qed.

  Definition modality_up1 :=
    Modality _ modality_up1_mixin.

  Definition modality_down1 :=
    Modality _ modality_down1_mixin.

End modalities.