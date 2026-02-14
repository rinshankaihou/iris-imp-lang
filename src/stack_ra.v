(* ghost state for environments *)
From iris.algebra Require Import excl auth gmap.
From iris.base_logic Require Import own.
From iris.bi Require Export monpred.
From iris.proofmode Require Export proofmode.

Section val.

Context {val : Type}.

Definition env_state := (gmap nat (gmap string val))%type.

Notation fixed_fracR A := (prodR (agreeR (leibnizO frac)) (prodR fracR A)).

Notation frameR := (gmapR string (exclR (leibnizO val))).

Definition envR := (authR (gmapUR nat (fixed_fracR frameR))).

Class envGS Σ := EnvGS {
  envGS_inG :: inG Σ envR;
  env_name : gname
}.

(* assertions are monPreds on stack level *)
Definition stack_index : biIndex := {| bi_index_type := nat; bi_index_rel := eq |}.

Definition assert `{!envGS Σ} := monPred stack_index (iPropI Σ).

Program Definition assert_of `{!envGS Σ} (P : nat -> iProp Σ) : assert := {| monPred_at := P |}.

Section env.

Context `{!envGS Σ}.

Definition env_auth (ρ : env_state) := own(inG0 := envGS_inG) env_name
 (●{dfrac.DfracOwn 1} ((λ r,
  (* use one extra share to remember the fraction *)
  let q := Qp.inv (pos_to_Qp (Pos.of_nat (1 + size r))) in
    (to_agree q, (1%Qp, (Excl <$> r : gmap _ (excl _))))) <$> ρ)).

Global Instance gmap_total `{Countable K} A : CmraTotal (iris.algebra.gmap.gmapR K A).
Proof. rewrite /CmraTotal /pcore /cmra_pcore /= /gmap.gmap_pcore_instance //. Qed.

Lemma Excl_fmap_incl : forall {A : ofe} (x y : option A), Excl <$> x ≼ Excl <$> y →
  match x with Some a => (x ≡ y)%stdpp | None => True end.
Proof.
  destruct x; last done; simpl.
  intros; destruct (Some_included_is_Some _ _ H) as (? & Heq).
  destruct y; inv Heq.
  by apply Excl_included in H as ->.
Qed.

Definition stack_frag n q0 q r := own(inG0 := envGS_inG) env_name (◯ {[n := (to_agree q0, (q, (Excl <$> r)))]}).

Definition points_to_var (id : string) (v : val) :=
  assert_of (λ n, ∃ q, stack_frag n q q {[id := v]})%I.

Definition env_to_environ (ρ : env_state) n : gmap string val :=
  match ρ !! n with Some r => r | None => ∅ end.

Lemma stack_frag_e' : forall ρ n q0 q r, env_auth ρ ∗ stack_frag n q0 q r ⊢
  ⌜let rho := env_to_environ ρ n in q0 = Qp.inv (pos_to_Qp (Pos.of_nat (1 + size rho))) ∧ r ⊆ rho⌝.
Proof.
  intros; rewrite /env_auth /stack_frag.
  iIntros "(H1 & H2)"; iDestruct (own_valid_2 with "H1 H2") as %((? & Heq & H)%gmap.singleton_included_l & _)%auth_both_valid_discrete; iPureIntro.
  rewrite lookup_fmap in Heq; rewrite /env_to_environ. destruct (ρ !! n) as [?|] eqn: Hn; rewrite !Hn in Heq |- *; inversion Heq as [?? HA |]; subst.
  rewrite -HA in H; clear Heq.
  apply Some_included in H as [(? & ? & Hr) | ?]; simpl in *.
  - apply to_agree_inj in H.
    apply (map_fmap_equiv_inj Excl), leibniz_equiv in Hr as ->; last apply Excl_inj; done.
  - apply prod_included in H as (Hq & H); apply prod_included in H as (_ & Hr); simpl in *.
    apply to_agree_included_L in Hq; split; first done.
    rewrite !gmap.lookup_included in Hr; intros i.
    specialize (Hr i); rewrite !lookup_fmap in Hr.
    apply (Excl_fmap_incl(A := leibnizO _)) in Hr.
    destruct (r !! i).
    * apply leibniz_equiv in Hr; rewrite -Hr //.
    * simpl; clear; destruct (_ !! _); done.
Qed.

Lemma stack_frag_e : forall ρ n q0 q r, env_auth ρ ∗ stack_frag n q0 q r ⊢
  ⌜let rho := env_to_environ ρ n in r ⊆ rho⌝.
Proof.
  intros; rewrite stack_frag_e'; apply bi.pure_mono; by intros (? & ?).
Qed.

Lemma stack_frag_e_1 : forall ρ n q0 r, env_auth ρ ∗ stack_frag n q0 1%Qp r ⊢
  ⌜let rho := env_to_environ ρ n in r = rho⌝.
Proof.
  intros; rewrite /env_auth /stack_frag.
  iIntros "(H1 & H2)"; iDestruct (own_valid_2 with "H1 H2") as %(H & Hvalid)%auth_both_valid_discrete.
  apply gmap.singleton_included_exclusive_l in H; [| apply _ | done].
  rewrite lookup_fmap in H; rewrite /env_to_environ. destruct (ρ !! n) as [?|] eqn: Hn; rewrite !Hn in H |- *; inversion H as [?? HA |]; subst.
  destruct HA as (_ & _ & Hr); simpl in *.
  apply (map_fmap_equiv_inj Excl), leibniz_equiv in Hr as ->; last apply Excl_inj; done.
Qed.

Lemma var_e : forall id v rho n, points_to_var id v n ∗ env_auth rho ⊢ ⌜(env_to_environ rho n) !! id = Some v⌝.
Proof.
  intros; rewrite /points_to_var /=.
  iIntros "((% & ?) & ?)"; iDestruct (stack_frag_e with "[$]") as %?%map_singleton_subseteq_l; done.
Qed.

Definition set_var (ρ : env_state) n i v :=
  match (ρ !! n)%stdpp with
  | Some r => <[n := <[i := v]>r]>ρ
  | None => ρ end.

Lemma var_update : forall ρ n i v v', env_auth ρ ∗ points_to_var i v n ⊢ |==> env_auth (set_var ρ n i v') ∗ points_to_var i v' n.
Proof.
  intros.
  iIntros "(Hr & Hi)".
  iDestruct (var_e with "[$Hr $Hi]") as %Hi.
  rewrite /env_to_environ in Hi.
  destruct (ρ !! n) as [r|] eqn: Hn; rewrite Hn in Hi; last by rewrite lookup_empty in Hi.
  rewrite /points_to_var /=.
  iDestruct "Hi" as (q) "Hi".
  iAssert (|==> env_auth (set_var ρ n i v') ∗ stack_frag n q q {[i := v']})%I with "[-]" as ">($ & $)"; last done.
  rewrite -own_op; iApply (own_update_2 with "Hr Hi").
  rewrite /set_var Hn /= !fmap_insert.
  eapply auth_update, (gmap.singleton_local_update(A := fixed_fracR frameR)).
  { rewrite lookup_fmap Hn //. }
  apply prod_local_update; simpl.
  - rewrite map_size_insert_Some //.
  - repeat (apply prod_local_update; first done); simpl.
    eapply (gmap.singleton_local_update(A := exclR (leibnizO _))).
    { rewrite lookup_fmap Hi //. }
    apply exclusive_local_update; done.
Qed.

Lemma stack_frag_join : forall n q0 q0' q1 q2 r1 r2,
  stack_frag n q0 q1 r1 ∗ stack_frag n q0' q2 r2 ⊢ ⌜q0 = q0' ∧ r1 ##ₘ r2⌝ ∧ stack_frag n q0 (q1 + q2)%Qp (r1 ∪ r2).
Proof.
  intros.
  rewrite /stack_frag -own_op -auth_frag_op gmap.singleton_op -!cmra.pair_op.
  iIntros "H"; iDestruct (own_valid with "H") as %(Hq & _ & Hr)%auth_frag_valid_1%gmap.singleton_valid; simpl in *.
  apply to_agree_op_inv_L in Hq as ->; rewrite agree_idemp !map_fmap_union.
  assert (r1 ##ₘ r2).
  { intros i; specialize (Hr i); rewrite gmap.lookup_op !lookup_fmap in Hr.
    destruct (r1 !! i), (r2 !! i); done. }
  rewrite !gmap.gmap_op_union; auto; by apply map_disjoint_fmap.
Qed.

Lemma stack_frag_split : forall n q0 q1 q2 r1 r2, r1 ##ₘ r2 →
  stack_frag n q0 (q1 ⋅ q2) (r1 ∪ r2) ⊢
  stack_frag n q0 q1 r1 ∗ stack_frag n q0 q2 r2.
Proof.
  intros.
  rewrite /stack_frag -own_op -auth_frag_op gmap.singleton_op -!cmra.pair_op agree_idemp.
  rewrite !map_fmap_union !gmap.gmap_op_union; auto; by apply map_disjoint_fmap.
Qed.

Lemma vars_equiv : forall lt lv n, length lt = length lv → NoDup lt →
  ([∗ list] i;v ∈ lt;lv, points_to_var i v n) ⊣⊢ if decide (length lt = O) then emp else
  ∃ q : frac, stack_frag n q (pos_to_Qp (Pos.of_nat (length lt)) * q)%Qp (list_to_map (zip lt lv)).
Proof.
  induction lt; destruct lv; inversion 1; simpl; first done.
  intros Hno; inv Hno; rewrite IHlt //.
  destruct (decide _).
  { rewrite e; destruct lt; last done; simpl.
    rewrite bi.sep_emp; do 2 f_equiv.
    rewrite Qp.mul_1_l //. }
  iSplit.
  - iIntros "((% & H) & Hrest)".
    iExists q; iDestruct "Hrest" as (q') "Hrest".
    iDestruct (stack_frag_join with "[$H $Hrest]") as ((<- & ?)) "H".
    rewrite -insert_union_singleton_l.
    replace (pos_to_Qp (Pos.of_nat (S (base.length lt)))) with (1 + pos_to_Qp (Pos.of_nat (base.length lt)))%Qp.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l //.
    { rewrite pos_to_Qp_add pos_to_Qp_inj_iff Nat2Pos.inj_succ //.
      rewrite Pplus_one_succ_l //. }
  - iIntros "(% & H)".
    rewrite bi.sep_exist_r; iExists q.
    rewrite bi.sep_exist_l; iExists q.
    iApply stack_frag_split.
    { apply map_disjoint_singleton_l_2.
      rewrite not_elem_of_list_to_map_1 //.
      intros ((?, ?) & ? & ?%elem_of_zip_l)%elem_of_list_fmap_2; simpl in *; congruence. }
    rewrite -insert_union_singleton_l.
    replace (pos_to_Qp (Pos.of_nat (S (length lt)))) with (1 + pos_to_Qp (Pos.of_nat (length lt)))%Qp.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l //.
    * rewrite pos_to_Qp_add pos_to_Qp_inj_iff Nat2Pos.inj_succ //.
      rewrite Pplus_one_succ_l //.
Qed.

Definition alloc_vars r n (ρ : env_state) := <[n := r]>ρ.

Lemma env_to_environ_alloc : forall r n ρ, env_to_environ (alloc_vars r n ρ) n = r.
Proof.
  intros; rewrite /env_to_environ /alloc_vars lookup_insert //.
Qed.

Lemma env_alloc : forall ρ n r, ρ !! n = None →
  env_auth ρ ⊢ |==> env_auth (<[n := r]> ρ) ∗ stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size r)))%Qp 1%Qp r.
Proof.
  intros.
  rewrite /env_auth /stack_frag -own_op; apply own_update.
  rewrite fmap_insert.
  apply auth_update_alloc, (gmap.alloc_singleton_local_update(A := fixed_fracR frameR)).
  * rewrite lookup_fmap H //.
  * split; [|split]; try done; simpl.
    intros i; rewrite /= lookup_fmap; destruct (_ !! i); done.
Qed.

Lemma env_to_environ_dealloc : forall n1 n2 ρ, n1 ≠ n2 → env_to_environ (delete n1 ρ) n2 = env_to_environ ρ n2.
Proof.
  intros; rewrite /env_to_environ /alloc_vars lookup_delete_ne //.
Qed.

Lemma env_dealloc : forall ρ n q r,
  env_auth ρ ∗ stack_frag n q 1%Qp r ⊢ |==> env_auth (delete n ρ).
Proof.
  intros.
  rewrite /env_auth /stack_frag -own_op; apply own_update.
  rewrite fmap_delete.
  apply auth_update_dealloc, (gmap.delete_singleton_local_update(A := fixed_fracR frameR)), _.
Qed.

(* going up/down 1 stack frame *)
Definition up1 (P : assert) : assert := assert_of (λ n, P (S n)).
Definition down1 (P : assert) : assert := assert_of (λ n, P (pred n)).

Global Instance up1_nonexpansive : NonExpansive up1.
Proof. split => ? /=. apply H. Qed.

Global Instance down1_nonexpansive : NonExpansive down1.
Proof. split => l /=. apply H. Qed.

Global Instance up1_proper : Proper (equiv ==> equiv) up1.
Proof. split => ? /=. apply H. Qed.

Global Instance down1_proper : Proper (equiv ==> equiv) down1.
Proof. split => l /=. apply H. Qed.

Lemma up1_mono : forall P Q, (P ⊢ Q) -> up1 P ⊢ up1 Q.
Proof. split => n; apply H. Qed.

Lemma down1_mono : forall P Q, (P ⊢ Q) -> down1 P ⊢ down1 Q.
Proof. split => n; apply H. Qed.

Lemma up1_objective : forall P `{!Objective P}, P ⊣⊢ up1 P.
Proof.
  intros. split => n.
  rewrite /up1 /=.
  iSplit; iApply objective_at.
Qed.

Lemma up1_obj_elim : forall P `{!Objective P}, up1 P ⊢ P.
Proof. intros; by rewrite -up1_objective. Qed.

Lemma down1_objective : forall P `{!Objective P}, P ⊣⊢ down1 P.
Proof.
  intros. split => n.
  rewrite /down1 /=.
  iSplit; iApply objective_at.
Qed.

Lemma down1_obj_elim : forall P `{!Objective P}, down1 P ⊢ P.
Proof. intros; by rewrite -down1_objective. Qed.

Lemma up1_down1 : forall P, up1 (down1 P) ⊣⊢ P.
Proof.
  intros. split => n. done.
Qed.

(* TODO: make IPM modality instances *)
Lemma up1_sep : forall P Q, up1 P ∗ up1 Q ⊣⊢ up1 (P ∗ Q).
Proof.
  intros. split => n.
  by rewrite /up1; monPred.unseal.
Qed.

Lemma down1_sep : forall P Q, down1 P ∗ down1 Q ⊣⊢ down1 (P ∗ Q).
Proof.
  intros. split => n.
  by rewrite /down1; monPred.unseal.
Qed.

Lemma up1_and : forall P Q, up1 P ∧ up1 Q ⊣⊢ up1 (P ∧ Q).
Proof.
  intros. split => n.
  by rewrite /up1; monPred.unseal.
Qed.

Lemma down1_and : forall P Q, down1 P ∧ down1 Q ⊣⊢ down1 (P ∧ Q).
Proof.
  intros. split => n.
  by rewrite /down1; monPred.unseal.
Qed.

Lemma up1_forall : forall {A} P, up1 (∀ x : A, P x) ⊣⊢ ∀ x, up1 (P x).
Proof.
  intros. split => n.
  by rewrite /up1; monPred.unseal.
Qed.

Lemma down1_forall : forall {A} P, down1 (∀ x : A, P x) ⊣⊢ ∀ x, down1 (P x).
Proof.
  intros. split => n.
  by rewrite /down1; monPred.unseal.
Qed.

Lemma up1_exist : forall {A} P, up1 (∃ x : A, P x) ⊣⊢ ∃ x, up1 (P x).
Proof.
  intros. split => n.
  by rewrite /up1; monPred.unseal.
Qed.

Lemma down1_exist : forall {A} P, down1 (∃ x : A, P x) ⊣⊢ ∃ x, down1 (P x).
Proof.
  intros. split => n.
  by rewrite /down1; monPred.unseal.
Qed.

Lemma up1_wand : forall P Q, up1 (P -∗ Q) ⊣⊢ (up1 P -∗ up1 Q).
Proof.
  intros. split => n.
  rewrite /up1; monPred.unseal.
  iSplit; iIntros "H" (? <-); by iApply "H".
Qed.

Lemma down1_wand : forall P Q, down1 (P -∗ Q) ⊣⊢ (down1 P -∗ down1 Q).
Proof.
  intros. split => n.
  rewrite /down1; monPred.unseal.
  iSplit; iIntros "H" (? <-); by iApply "H".
Qed.

Global Instance up1_persistent P `{!Persistent P} : Persistent (up1 P).
Proof.
  by apply monPred_persistent; intros; simpl; apply monPred_at_persistent.
Qed.

Lemma up1_persistently P : up1 (<pers> P) ⊣⊢ <pers> (up1 P).
Proof.
  intros. split => n.
  by rewrite /up1; monPred.unseal.
Qed.

Lemma up1_affinely P : up1 (<affine> P) ⊣⊢ <affine> (up1 P).
Proof.
  intros. split => n. 
  rewrite /up1 /= !monPred_at_affinely //.
Qed.

Lemma up1_intuitionistically P : up1 (□ P) ⊣⊢ □ (up1 P).
Proof.
  intros.
   rewrite /bi_intuitionistically up1_affinely up1_persistently //.
Qed.

Global Instance down1_persistent P `{!Persistent P} : Persistent (down1 P).
Proof.
  by apply monPred_persistent; intros; simpl; apply monPred_at_persistent.
Qed.

Lemma up1_later : forall P, up1 (▷ P) ⊣⊢ ▷ (up1 P).
Proof.
  intros. split => n.
  by rewrite /up1; monPred.unseal.
Qed.

Lemma down1_later : forall P, down1 (▷ P) ⊣⊢ ▷ (down1 P).
Proof.
  intros. split => n.
  by rewrite /down1; monPred.unseal.
Qed.

Lemma up1_bupd : forall P, up1 (|==> P) ⊣⊢ |==> (up1 P).
Proof.
  intros. split => n.
  by rewrite /up1; monPred.unseal.
Qed.

Lemma down1_bupd : forall P, down1 (|==> P) ⊣⊢ |==> (down1 P).
Proof.
  intros. split => n.
  by rewrite /down1; monPred.unseal.
Qed.

End env.

Lemma env_init0 `{inG Σ envR} : ⊢ |==> ∃ H : envGS Σ, env_auth ∅.
Proof.
  iMod (own_alloc(A := envR) (● ∅)) as (γe) "?".
  { by rewrite auth_auth_valid. }
  iModIntro; iExists (EnvGS _ _ γe); iFrame.
Qed.

Lemma env_init `{inG Σ envR} (r : gmap string val) : ⊢ |==> ∃ H : envGS Σ,
  env_auth {[O := r]} ∗ ∃ q, stack_frag O q 1%Qp r.
Proof.
  iMod (own_alloc(A := envR) (● {[O := (to_agree (/ pos_to_Qp (Pos.of_nat (S (size r))))%Qp, (1%Qp, Excl <$> r))]} ⋅
    ◯ {[O := (to_agree (/ pos_to_Qp (Pos.of_nat (S (size r))))%Qp, (1%Qp, Excl <$> r))]})) as (γe) "(? & ?)".
  { rewrite auth_both_valid_discrete; split => //=.
    rewrite singleton_valid; repeat split => //=.
    intros i; rewrite lookup_fmap; destruct (r !! i); done. }
  iModIntro; iExists (EnvGS _ _ γe); iFrame.
Qed.

End val.

Arguments envGS : clear implicits.
Global Instance: Params (@points_to_var) 3 := {}.
Global Opaque points_to_var.

Notation "⇓ P" := (down1 P) (at level 20) : bi_scope.
Notation "⇑ P" := (up1 P) (at level 20): bi_scope.
Notation "l ↦v v" := (points_to_var l v)
  (at level 20, format "l  ↦v  v") : bi_scope.
