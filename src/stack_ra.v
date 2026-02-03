(* ghost state for environments *)
From iris.algebra Require Import excl auth gmap.
From iris_simp_lang Require Import implang.

Definition env_state := (gmap nat (gmap string val))%type.

Notation fixed_fracR A := (prodR (agreeR (leibnizO frac)) (prodR fracR A)).

Notation frameR := (gmapR string (exclR (leibnizO val))).

Notation envR := (authR (gmapUR nat (fixed_fracR frameR))).

Class envGS Σ := EnvGS {
  envGS_inG :: inG Σ envR;
  env_name : gname
}.

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
  assert_of (λ n, ∃ q, stack_frag n q q {[id := v]}).

Lemma stack_frag_e' : forall ρ n q0 q r, env_auth ρ ∗ stack_frag n q0 q r ⊢
  ⌜let rho := env_to_environ ρ n in q0 = Qp.inv (pos_to_Qp (Pos.of_nat (1 + size rho))) ∧ r ⊆ rho⌝.
Proof.
  intros; rewrite /env_auth /stack_frag.
  iIntros "(H1 & H2)"; iDestruct (own_valid_2 with "H1 H2") as %(_ & ((? & Heq & H)%gmap.singleton_included_l & _)%auth_both_valid_discrete); iPureIntro.
  rewrite lookup_fmap in Heq; rewrite /env_to_environ. destruct (snd ρ !! n)%stdpp as [(?, ?)|] eqn: Hn; rewrite !Hn in Heq |- *; inversion Heq as [?? HA |]; subst.
  rewrite -HA in H; clear Heq.
  apply Some_included in H as [(? & ? & Hv & Ht) | ?]; simpl in *.
  - apply to_agree_inj in H.
    apply (map_fmap_equiv_inj Excl), leibniz_equiv in Hv as ->; last apply Excl_inj.
    apply (map_fmap_equiv_inj Excl), leibniz_equiv in Ht as ->; last apply Excl_inj; done.
  - apply prod_included in H as (Hq & H); apply prod_included in H as (_ & H); apply prod_included in H as (Hv & Ht); simpl in *.
    apply to_agree_included_L in Hq; split; first done.
    rewrite !gmap.lookup_included in Hv Ht; split; intros i.
    + specialize (Hv i); rewrite !lookup_fmap in Hv.
      apply (Excl_fmap_incl(A := leibnizO _)) in Hv.
      destruct (ve !! i)%stdpp.
      * apply leibniz_equiv in Hv; rewrite -Hv //.
      * simpl; clear; destruct (_ !! _)%stdpp; done.
    + specialize (Ht i); rewrite !lookup_fmap in Ht.
      apply (Excl_fmap_incl(A := leibnizO _)) in Ht.
      destruct (te !! i)%stdpp.
      * apply leibniz_equiv in Ht; rewrite -Ht //.
      * simpl; clear; destruct (_ !! _)%stdpp; done.
Qed.

Lemma stack_frag_e : forall ρ n q0 q r, env_auth ρ ∗ stack_frag n q0 q r ⊢
  ⌜let rho := env_to_environ ρ n in r ⊆ rho⌝.
Proof.
  intros; rewrite stack_frag_e'; apply bi.pure_mono; tauto.
Qed.

Lemma stack_frag_e_1 : forall ρ n q0 r, env_auth ρ ∗ stack_frag n q0 1%Qp r ⊢
  ⌜let rho := env_to_environ ρ n in r = rho⌝.
Proof.
  intros; rewrite /env_auth /stack_frag.
  iIntros "(H1 & H2)"; iDestruct (own_valid_2 with "H1 H2") as %(_ & (H & Hvalid)%auth_both_valid_discrete).
  apply gmap.singleton_included_exclusive_l in H; [| apply _ | done].
  rewrite lookup_fmap in H; rewrite /env_to_environ. destruct (snd ρ !! n)%stdpp as [(?, ?)|] eqn: Hn; rewrite !Hn in H |- *; inversion H as [?? HA |]; subst.
  destruct HA as (_ & _ & Hv & Ht); simpl in *.
  apply (map_fmap_equiv_inj Excl), leibniz_equiv in Hv as ->; last apply Excl_inj.
  apply (map_fmap_equiv_inj Excl), leibniz_equiv in Ht as ->; last apply Excl_inj; done.
Qed.

Lemma var_e : forall id v rho n, points_to_var id v n ∗ env_auth rho ⊢ ⌜(env_to_environ rho n) !! id = Some v⌝.
Proof.
  intros; rewrite /temp /=.
  iIntros "((% & ?) & ?)"; iDestruct (stack_frag_e with "[$]") as %(_ & ?%map_singleton_subseteq_l); done.
Qed.

Definition set_temp (ρ : env_state) n i v :=
  match (ρ !! n)%stdpp with
  | Some r => <[n := <[i := v]>r]>ρ
  | None => ρ end.

Lemma var_update : forall ρ n i v v', env_auth ρ ∗ points_to_var i v n ⊢ |==> env_auth (set_temp ρ n i v') ∗ points_to_var i v' n.
Proof.
  intros.
  iIntros "(Hr & Hi)".
  iDestruct (temp_e with "[$Hr $Hi]") as %Hi.
  rewrite /env_to_environ in Hi.
  destruct (snd ρ !! n)%stdpp as [(?, te)|] eqn: Hn; rewrite Hn in Hi; last by rewrite lookup_empty in Hi.
  rewrite /temp /=.
  iDestruct "Hi" as (q) "Hi".
  iAssert (|==> env_auth (set_temp ρ n i v') ∗ stack_frag n q q ∅ {[i := v']}) with "[-]" as ">($ & $)"; last done.
  rewrite -own_op; iApply (own_update_2 with "Hr Hi").
  rewrite /set_temp.
  destruct ρ as (?, s); rewrite Hn /=.
  apply prod_update; first done.
  rewrite /= !fmap_insert.
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
  rewrite /stack_frag -own_op -cmra.pair_op -auth_frag_op gmap.singleton_op -!cmra.pair_op.
  iIntros "H"; iDestruct (own_valid with "H") as %(_ & (Hq & _ & Hv & Ht)%auth_frag_valid_1%gmap.singleton_valid); simpl in *.
  apply to_agree_op_inv_L in Hq as ->; rewrite agree_idemp !map_fmap_union.
  assert (ve1 ##ₘ ve2).
  { intros i; specialize (Hv i); rewrite gmap.lookup_op !lookup_fmap in Hv.
    destruct (ve1 !! i)%stdpp, (ve2 !! i)%stdpp; done. }
  assert (te1 ##ₘ te2).
  { intros i; specialize (Ht i); rewrite gmap.lookup_op !lookup_fmap in Ht.
    destruct (te1 !! i)%stdpp, (te2 !! i)%stdpp; done. }
  rewrite !gmap.gmap_op_union; auto; by apply map_disjoint_fmap.
Qed.

Lemma stack_frag_split : forall n q0 q1 q2 r1 r2, r1 ##ₘ r2 →
  stack_frag n q0 (q1 ⋅ q2) (r1 ∪ r2) ⊢
  stack_frag n q0 q1 r1 ∗ stack_frag n q0 q2 r2.
Proof.
  intros.
  rewrite /stack_frag -own_op -cmra.pair_op -auth_frag_op gmap.singleton_op -!cmra.pair_op agree_idemp.
  rewrite !map_fmap_union !gmap.gmap_op_union; auto; by apply map_disjoint_fmap.
Qed.

Lemma vars_equiv : forall lt lv n, length lt = length lv → list_norepet lt →
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
    iDestruct (stack_frag_join with "[$H $Hrest]") as ((<- & ? & _)) "H".
    rewrite -insert_union_singleton_l.
    replace (pos_to_Qp (Pos.of_nat (S (base.length lt)))) with (1 + pos_to_Qp (Pos.of_nat (base.length lt)))%Qp.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l //.
    { rewrite pos_to_Qp_add pos_to_Qp_inj_iff Nat2Pos.inj_succ //.
      rewrite Pplus_one_succ_l //. }
  - iIntros "(% & H)".
    rewrite bi.sep_exist_r; iExists q.
    rewrite bi.sep_exist_l; iExists q.
    iApply stack_frag_split.
    { done. }
    { apply map_disjoint_singleton_l_2.
      rewrite not_elem_of_list_to_map_1 //.
      intros ((?, ?) & ? & ?%elem_of_zip_l%elem_of_list_In)%elem_of_list_fmap_2; simpl in *; congruence. }
    rewrite -insert_union_singleton_l.
    replace (pos_to_Qp (Pos.of_nat (S (length lt)))) with (1 + pos_to_Qp (Pos.of_nat (length lt)))%Qp.
    rewrite Qp.mul_add_distr_r Qp.mul_1_l //.
    * rewrite pos_to_Qp_add pos_to_Qp_inj_iff Nat2Pos.inj_succ //.
      rewrite Pplus_one_succ_l //.
Qed.

Definition alloc_vars r n (ρ : env_state) := <[n := r]>ρ.

Lemma env_to_environ_alloc : forall ve te n ρ, env_to_environ (alloc_vars r n ρ) n = r.
Proof.
  intros; rewrite /env_to_environ /alloc_vars lookup_insert //.
Qed.

Lemma env_alloc : forall ρ n r, ρ !! n = None →
  env_auth ρ ⊢ |==> env_auth (<[n := r]> ρ) ∗ stack_frag n (/ pos_to_Qp (Pos.of_nat (1 + size r)))%Qp 1%Qp r.
Proof.
  intros.
  rewrite /env_auth /stack_frag -own_op; apply own_update.
  apply prod_update; simpl; first reflexivity.
  rewrite fmap_insert.
  apply auth_update_alloc, (gmap.alloc_singleton_local_update(A := fixed_fracR frameR)).
  * rewrite lookup_fmap H //.
  * split3; try done; simpl.
    split; intros i; rewrite /= lookup_fmap; destruct (_ !! i)%stdpp; done.
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
  apply prod_update; simpl; first reflexivity.
  rewrite fmap_delete.
  apply auth_update_dealloc, (gmap.delete_singleton_local_update(A := fixed_fracR frameR)), _.
Qed.

End env.

Global Instance: Params (@points_to_var) 2 := {}.
Global Opaque points_to_var.
