From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import wsat invariants saved_prop.
From iris.algebra Require Import auth excl gmap frac_agree.
From machine_program_logic.program_logic Require Export weakestpre.
Import uPred.

(* move to stdpp *)
Section big_opL.
  Context {M : ofe} (o : M → M → M) `{!Monoid o}.

  Lemma big_opL_filter {A} (φ : A → M) (P : A → Prop) `{!∀ a, Decision (P a)} l :
    ([^o list] a ∈ filter P l, φ a) ≡
    [^o list] a ∈ l, if bool_decide (P a) then φ a else monoid_unit.
  Proof.
    induction l as [|a l IHl]; simpl; first done.
    destruct (decide (P a)).
    - rewrite filter_cons_True; last done.
      rewrite bool_decide_eq_true_2; last done.
      rewrite /=.
      apply ne_proper_2; [apply monoid_ne|done|done].
    - rewrite filter_cons_False; last done.
      rewrite bool_decide_eq_false_2; last done.
      rewrite monoid_left_id; done.
  Qed.

  Lemma big_opL_seq {A} s n (φ : nat → M) (l : list A) :
    n = length l →
    ([^o list] a ∈ seq s n, φ a) ≡ [^o list] i ↦ _ ∈ l, φ (s + i).
  Proof.
    revert s l; induction n as [|n IHn]; intros s l Hnl; first by destruct l.
    destruct l; simpl in *; first done.
    rewrite Nat.add_0_r.
    apply ne_proper_2; [apply monoid_ne|done|].
    setoid_rewrite <- Nat.add_succ_comm; eauto.
  Qed.

End big_opL.

(* also move to stdpp *)
Lemma bool_decide_of_eq_true b : bool_decide (b = true) = b.
Proof. destruct b; done. Qed.

Section adequacy.
Context `{!irisG M Σ}.
Implicit Types m : mode M.
Implicit Types σ : state M.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : mode M → iProp Σ.
Implicit Types Φs : list (mode M → iProp Σ).

Definition wpvm σ id m Φ : iProp Σ :=
  ((∃ P, VMPropAuth id P) ∗
   if terminated m then Φ m else
     ((if scheduled σ id then True else VMProp_holds id (1/2)%Qp) -∗ WP m @ id; ⊤ {{ Φ }}))%I.

Notation wpvms_convid f σ t Φs := ([∗ list] id ↦ m;Φ ∈ t;Φs, wpvm σ (f id) m Φ)%I.

Notation wpvms σ t Φs := ([∗ list] id ↦ m;Φ ∈ t;Φs, wpvm σ id m Φ)%I.

Lemma wp_step n id m1 σ1 m2 σ2 Φ :
  scheduled σ1 id →
  prim_step m1 σ1 m2 σ2 →
  state_interp n σ1 -∗ wpvm σ1 id m1 Φ
    ={⊤,∅}=∗ |={∅}▷=> |={∅,⊤}=>
    ([∗ list] vmid ∈ just_scheduled_vms n σ1 σ2, VMProp_holds vmid (1/2)%Qp) ∗
    state_interp n σ2 ∗ wpvm σ2 id m2 Φ.
Proof.
  iIntros (? ?) "Hσ [HPA H]".
  rewrite (terminated_stuck m1 σ1 m2 σ2) //.
  rewrite /wpvm {1}wp_unfold /wp_pre.
  rewrite (terminated_stuck m1 σ1 m2 σ2) //.
  destruct (scheduled σ1 id) eqn:Hsch; last done.
  iMod ("H" with "[//] [] Hσ") as "(_ & H)"; first by rewrite Hsch.
  iModIntro.
  iMod ("H" with "HPA [//]") as "H".
  iModIntro; iNext; iModIntro.
  iMod "H" as "($ & $ & $ & H)".
  destruct (scheduled σ2 id); destruct (terminated m2) eqn:Hterm;
    simpl; [|done| |done]; rewrite wp_unfold /wp_pre Hterm; iApply "H"; done.
Qed.

Lemma wpvm_step_by_other id m σ1 σ2 Φ :
  wpvm σ1 id m Φ -∗
  (if just_scheduled σ1 σ2 id then VMProp_holds id (1/2)%Qp else emp) -∗
  wpvm σ2 id m Φ.
Proof.
  rewrite /wpvm.
  iIntros "[HPA Hwp]".
  rewrite /just_scheduled.
  destruct (scheduled σ1 id) eqn:Hsch1; destruct (terminated m) eqn:Hsterm;
    simpl; iFrame; [done| |by auto|].
  - iIntros "_"; iFrame; iIntros "?"; iApply "Hwp"; done.
  - destruct (scheduled σ2 id) eqn:Hsch2; simpl.
    + iFrame. iIntros "? _"; iApply "Hwp"; done.
    + iIntros "_"; iFrame.
Qed.

Lemma wpvms_step_by_other f ms σ1 σ2 Φs :
  wpvms_convid f σ1 ms Φs -∗
  ([∗ list] id ↦ _ ∈ ms, (if just_scheduled σ1 σ2 (f id) then VMProp_holds (f id) (1/2)%Qp else emp)) -∗
  wpvms_convid f σ2 ms Φs.
Proof.
  iInduction ms as [|vm ms] "IH" forall (f Φs).
  - iIntros "H". iDestruct (big_sepL2_nil_inv_l with "H") as %->; simpl; auto.
  - iIntros "H".
    iDestruct (big_sepL2_cons_inv_l with "H") as (Φ Φs' ->) "[Hvm Hvms]".
    iIntros "[Hvmjsch Hvmsjsch]".
    iSplitL "Hvm Hvmjsch"; first by iApply (wpvm_step_by_other with "[$] [$]").
    iApply ("IH" with "[$] [$]").
Qed.

Lemma wpvms_step n ms1 ms2 σ1 σ2 Φs :
  n = length ms1 →
  step (ms1,σ1) (ms2, σ2) →
  state_interp n σ1 -∗
  wpvms σ1 ms1 Φs -∗
  |={⊤,∅}=> |={∅}▷=> |={∅,⊤}=> state_interp n σ2 ∗ wpvms σ2 ms2 Φs.
Proof.
  iIntros (Hn Hstep) "Hσ Ht".
  destruct Hstep as [m1' σ1' m2' σ2' t2' t3 Hstep]; simplify_eq/=.
  iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[Ht2' Ht]".
  iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht Ht3]".
  rewrite Nat.add_0_r.
  iMod (wp_step with "Hσ Ht") as ">H"; [by rewrite Hstep|done|].
  iModIntro; iModIntro; iNext; iMod "H"; iModIntro.
  iMod "H" as "(Hjsch & $ & H)".
  iModIntro.
  rewrite /just_scheduled_vms big_opL_filter big_opL_seq /=; last done.
  rewrite big_sepL_app.
  iDestruct "Hjsch" as "[Hjscht2' [Hjsch Hjscht3]]".
  iApply (big_sepL2_app with "[Ht2' Hjscht2']").
  { iApply (wpvms_step_by_other (λ x, x) with "[$]").
    erewrite big_opL_ext; [done|by intros ???; rewrite bool_decide_of_eq_true]. }
  iSplitL "H"; first by rewrite Nat.add_0_r.
  iApply (wpvms_step_by_other with "[$]").
  erewrite big_opL_ext; [done|by intros ???; rewrite bool_decide_of_eq_true].
Qed.

(* if we want to support dynamic creation VM's at some point we need to *)
(* strengthen the next tow lemmas. *)
Lemma step_preserve_vms_length ms1 σ1 ms2 σ2 :
  step (ms1, σ1) (ms2, σ2) → length ms1 = length ms2.
Proof.
  inversion 1; simplify_eq.
  rewrite !app_length; done.
Qed.

Lemma nsteps_preserve_vms_length n ms1 σ1 ms2 σ2 :
  nsteps step n (ms1, σ1) (ms2, σ2) → length ms1 = length ms2.
Proof.
  revert ms1 σ1 ms2 σ2; induction n as [|n IHn]; intros ms1 σ1 ms2 σ2;
    inversion 1 as [|?? [] ?]; subst; first done.
  etrans; first by eapply step_preserve_vms_length.
  eapply IHn; eauto.
Qed.

Lemma wpvms_steps k n ms1 ms2 σ1 σ2 Φs :
  n = length ms1 →
  nsteps step k (ms1, σ1) (ms2, σ2) →
  state_interp n σ1 -∗ wpvms σ1 ms1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^k |={∅,⊤}=> state_interp n σ2 ∗ wpvms σ2 ms2 Φs.
Proof.
  revert ms1 ms2 σ1 σ2 Φs.
  induction k as [|k IHk]=> ms1 ms2 σ1 σ2 Φs Hlen /=.
  { inversion_clear 1; iIntros "? ?". iFrame.
    iMod (fupd_mask_subseteq ∅) as "H"; first done. by iFrame. }
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  iDestruct (wpvms_step with "Hσ He") as ">H"; [done|done|].
  iModIntro. iApply step_fupd_fupd. iApply (step_fupd_wand with "H").
  iIntros ">[Hσ He]".
  iMod (IHk with "Hσ He") as "IH";
    [by erewrite <- step_preserve_vms_length; eauto|done|iModIntro].
  iApply (step_fupdN_wand with "IH"). iIntros ">[$ $]"; done.
Qed.

Lemma wp_not_stuck n id m σ Φ :
  scheduled σ id →
  state_interp n σ -∗ WP m @ id {{ Φ }} ={⊤}=∗ ⌜not_stuck m σ⌝.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck. iIntros (?) "Hσ H".
  destruct (terminated m) eqn:?; first by eauto.
  iSpecialize ("H" $! _ σ with "[//] Hσ"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wpvms_strong_adequacy k n Φs ms1 ms2 σ1 σ2 :
  n = length ms1 →
  nsteps step k (ms1, σ1) (ms2, σ2) →
  state_interp n σ1 -∗ wpvms σ1 ms1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^k |={∅,⊤}=>
    ⌜∀ i m2, scheduled σ2 i → ms2 !! i = Some m2 → not_stuck m2 σ2⌝ ∗
    state_interp n σ2 ∗
    [∗ list] m;Φ ∈ ms2;Φs,
      from_option Φ True (if terminated m then Some m else None).
Proof.
  iIntros (Hlen Hstep) "Hσ He". iMod (wpvms_steps with "Hσ He") as "Hwp"; [done|done|].
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as "(Hσ & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ i m2, scheduled σ2 i → ms2 !! i = Some m2 → not_stuck m2 σ2 ⌝%I
    (state_interp (length ms1) σ2 ∗ wpvms σ2 ms2 Φs)%I
    with "[$Hσ $Ht]") as "(%&Hσ&Hwp)".
  { iIntros "(Hσ & Ht)" (i m' Hm'sch Hm').
    move: Hm' => /(elem_of_list_split_length _ _ _)[?[?[-> ?]]]; subst.
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ?) "[? Hwp]".
    iDestruct (big_sepL2_cons_inv_l with "Hwp") as (Φ Φs3 ->) "[Hwp ?]".
    rewrite Nat.add_0_r.
    iMod (wp_not_stuck with "Hσ [Hwp]") as "$"; [done| |done].
    rewrite /wpvm.
    iDestruct "Hwp" as "[_ Hwp]".
    destruct terminated eqn:Hterm.
    - rewrite wp_unfold /wp_pre Hterm; eauto.
    - destruct scheduled; last done.
      iApply "Hwp"; done. }
  iSplitR; first done. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Hwp").
  iIntros "!#" (vmid m Φ ? ?) "Hwp".
  destruct (terminated m) eqn:Hm2'; last done.
  simpl. iApply (wp_terminated_inv' vmid); first done.
  rewrite /wpvm.
  iDestruct "Hwp" as "[_ Hwp]".
  rewrite Hm2'.
  rewrite wp_unfold /wp_pre Hm2'; eauto.
Qed.
End adequacy.

Class irisPreGS (Σ : gFunctors) := IrisPreG {
  iris_invPreGS :> invGpreS Σ;
  irisG_saved_prop :> savedPropG Σ;
  irisG_prop_name :> inG Σ (authUR (optionUR (frac_agreeR gnameO)));
  irisG_name_map :> inG Σ (authUR (gmapUR nat (agreeR gnameO)));
}.

Definition irisΣ :=
  #[invΣ; savedPropΣ; GFunctor (authUR (optionUR (frac_agreeR gnameO)));
    GFunctor (authUR (gmapUR nat (agreeR gnameO)))].

Global Instance iris_subG Σ : subG irisΣ Σ → irisPreGS Σ.
Proof. solve_inG. Qed.

Lemma allocated_props `{!irisPreGS Σ} n (N : gmap nat gname) (Ps : list (iProp Σ)) γ :
  let VMProp γNN id P :=
      (∃ (γvmn : gname) (γ : gnameO),
        own γNN (◯ {[id := to_agree γvmn]})
            ∗ own γvmn (◯ (Some (to_frac_agree 1 γ))) ∗ saved_prop_own γ P)%I
  in
  let VMPropAuth γNN id P :=
      (∃ (γvmn : gname) (γ : gnameO),
        own γNN (◯ {[id := to_agree γvmn]})
            ∗ own γvmn (● (Some (to_frac_agree 1 γ))) ∗ saved_prop_own γ P)%I
  in
  own γ (● (to_agree <$> N : gmapUR nat (agreeR gnameO))) -∗
  ⌜∀ k, k ∈ dom (gset nat) N ↔ k < n⌝ ==∗
    ∃ (M : gmap nat gname),
      ⌜∀ k, k ∈ dom (gset nat) M ↔ k < n + length Ps ⌝ ∗
      own γ (● (to_agree <$> M : gmapUR nat (agreeR gnameO))) ∗
      ([∗ list] id↦P ∈ Ps, VMProp γ (n + id) P) ∗
      ([∗ list] id↦P ∈ Ps, VMPropAuth γ (n + id) P).
Proof.
  iIntros "Hγ %HN".
  iInduction Ps as [|P Ps] "IH" forall (n N HN).
  - simpl; iModIntro; iExists N; iFrame.
    iSplit; last done.
    iPureIntro.
    intros ?; rewrite HN; lia.
  - iMod (saved_prop_alloc P) as (γP) "#HP".
    iMod (own_alloc ((● (Some (to_frac_agree 1%Qp γP))) ⋅ (◯ (Some (to_frac_agree 1%Qp γP))))) as (γPe) "[HγPeF HγPe]".
    { apply auth_both_valid; done. }
    iMod (own_update
            _ _ (● (to_agree <$> <[n := γPe]>N : gmapUR nat (agreeR gnameO))
                   ⋅ ◯ {[ n := to_agree γPe]}) with "Hγ") as "[Hγ #HγP]".
    { rewrite fmap_insert.
      apply auth_update_alloc, alloc_local_update; last done.
      apply not_elem_of_dom.
      rewrite dom_fmap HN; lia. }
    iMod ("IH" $! (S n) _ with "[] Hγ") as (M) "(%Hdom & Hγ & HPs & HPsF)".
    { iPureIntro; intros ?. rewrite dom_insert_L elem_of_union elem_of_singleton HN; lia. }
    iModIntro; iExists _; iFrame "Hγ".
    iSplit.
    { iPureIntro; simpl; split; rewrite Hdom; lia. }
    rewrite /= !Nat.add_0_r.
    setoid_rewrite <- Nat.add_succ_comm.
    iSplitR "HγPeF HPsF"; [iFrame "HPs"|iFrame "HPsF"];
      iExists _, _; iFrame; iFrame "#".
Qed.

(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy Σ M `{!irisPreGS Σ} ms1 σ1 n ms2 σ2 φ :
  (∀ `{Hinv : !invGS Σ},
      ⊢ |={⊤}=>
         ∀ name_map_name,
         ∃
         (stateI : nat → state M → iProp Σ)
         (Φs : list (mode M → iProp Σ)),
         let _ : irisG M Σ := IrisG _ _ Hinv _ _ _ name_map_name stateI in
         |={⊤}=> ∃ (Ps : list (iProp Σ)),
       ⌜length Ps = length ms1⌝ ∗
       stateI (length ms1) σ1 ∗
       (([∗ list] id ↦ P ∈ Ps, VMProp id P 1) -∗
           [∗ list] id ↦ m;Φ ∈ ms1;Φs,
             if terminated m then
                Φ m
              else (if (scheduled σ1 id) then True else VMProp_holds id (1/2)%Qp) -∗
              WP m @ id; ⊤ {{ Φ }}) ∗
       ( (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ ∀ i m2, scheduled σ2 i → ms2 !! i = Some m2 → not_stuck m2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI (length ms1) σ2 -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         ([∗ list] m;Φ ∈ ms2;Φs, from_option Φ True (if terminated m then Some m else None)) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps step n (ms1, σ1) (ms2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  apply (step_fupdN_soundness _ (S n))=> Hinv.
  iMod Hwp as "Hwp".
  iMod (own_alloc (● ∅)) as (name_map_name) "HNNF".
  { apply auth_auth_valid; done. }
  iDestruct ("Hwp" $! name_map_name) as (stateI Φs) ">Hwp".
  clear Hwp.
  iDestruct "Hwp" as (Ps Hlen) "(Hσ & Hwp & Hφ)".
  iEval (rewrite -(fmap_empty to_agree)) in "HNNF".
  iMod (allocated_props 0 ∅ Ps with "HNNF []") as (?) "(_ & HNNF & HPs & HPsF)".
  { iPureIntro; intros ?; rewrite dom_empty; split; [set_solver|lia]. }
  simpl.
  iSpecialize ("Hwp" with "HPs").
  set (IG := IrisG _ _ Hinv _ _ _ name_map_name stateI).
  iDestruct (big_sepL2_length with "Hwp") as %HΦs.
  iAssert ([∗ list] id↦m;_ ∈ ms1;Φs, ∃ P, VMPropAuth id P)%I with "[HPsF]" as "HPsF".
  { clear -Ps Hlen Φs HΦs.
    iStopProof.
    change (([∗ list] id↦P ∈ Ps, ∃ (γvmn : gname) (γ : gnameO),
                         own name_map_name (◯ {[0 + id := to_agree γvmn]})
                         ∗ own γvmn (● (Some (to_frac_agree 1 γ))) ∗ saved_prop_own γ P)
              -∗ [∗ list] id↦_;_ ∈ ms1;Φs, ∃ (P : iProp Σ), VMPropAuth (0 + id) P).
    generalize 0 as k.
    revert Ps Hlen Φs HΦs.
    induction ms1 as [|m ms1 IHms1]; iIntros (Ps Hlen Φs HΦs k) "HPsF".
    - destruct Φs; done.
    - destruct Φs; first done.
      destruct Ps; first done.
      simpl in *.
      iDestruct "HPsF" as "[HPF HPsF]".
      iSplitR "HPsF".
      + iExists _; iFrame.
      + setoid_rewrite <- Nat.add_succ_comm.
        iApply (IHms1 Ps); [lia|lia|done]. }
  iCombine "HPsF Hwp" as "Hwp".
  rewrite -big_sepL2_sep.
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wpvms_strong_adequacy _ _ IG _ with "Hσ Hwp")
    as "H"; [done|done|].
  iAssert (|={∅}▷=>^(S n) |={∅}=> ⌜φ⌝)%I with "[-]" as "H"; last first.
  { by iApply step_fupdN_S_fupd. }
  iApply (step_fupdN_wand with "H").
  iModIntro; iNext; iModIntro.
  iMod 1 as (?) "(Hσ & Ht2) /=".
  iDestruct (big_sepL2_length with "Ht2") as %Hlent2.
  rewrite -Hlen1 in Hlent2.
  iApply ("Hφ" with "[//] Hσ"); done.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {M} (ms1 : list (mode M)) (σ1 : state M)
    (φs : list (mode M → state M → Prop)) := {
  adequate_result ms2 σ2 :
   rtc step (ms1, σ1) (ms2, σ2) →
   (Forall2
      (λ m2 φ, from_option
                 (λ m, φ m σ2)
                 True
                 (if terminated m2 then Some m2 else None)) ms2 φs);
  adequate_not_stuck i ms2 σ2 m2 :
   rtc step (ms1, σ1) (ms2, σ2) →
   scheduled σ2 i → ms2 !! i = Some m2 → not_stuck m2 σ2
}.

Lemma adequate_alt {M} ms1 σ1 (φs : list (mode M → state M → Prop)) :
  adequate ms1 σ1 φs ↔ ∀ ms2 σ2,
    rtc step (ms1, σ1) (ms2, σ2) →
    (Forall2
       (λ m2 φ, from_option
                  (λ m, φ m σ2)
                  True
                  (if terminated m2 then Some m2 else None)) ms2 φs) ∧
      (∀ i m2, scheduled σ2 i → ms2 !! i = Some m2 → not_stuck m2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_safe {M} (ms1 : list (mode M)) ms2 σ1 σ2 φs :
  adequate ms1 σ1 φs →
  rtc step (ms1, σ1) (ms2, σ2) →
  ∀ i m2, ms2 !! i = Some m2 →
          terminated m2 = true ∨
          (scheduled σ2 i → ∃ m3 σ3, prim_step m2 σ2 m3 σ3).
Proof.
  rewrite adequate_alt.
  intros Had Hsteps.
  apply Had in Hsteps as [_ Hnstk].
  intros i m2 Hm2.
  destruct (terminated m2) eqn:Hm2ter; first by left.
  right.
  intros Hsch.
  destruct (Hnstk i m2 Hsch Hm2) as [Hn1|Hn2]; last by eauto.
  rewrite Hm2ter in Hn1; done.
Qed.

Corollary wp_adequacy Σ M `{!irisPreGS Σ} ms σ φs :
  length ms = length φs →
  (∀ `{Hinv : !invGS Σ},
     ⊢ |={⊤}=> ∀ name_map_name,
         ∃
         (stateI : nat → state M → iProp Σ),
         let _ : irisG M Σ := IrisG _ _ Hinv _ _ _ name_map_name stateI in
         |={⊤}=> ∃ (Ps : list (iProp Σ)),
       ⌜length Ps = length ms⌝ ∗
       stateI (length ms) σ ∗
       (([∗ list] id ↦ P ∈ Ps, VMProp id P 1) -∗
           [∗ list] id ↦ m;Φ ∈ ms;φs,
             if terminated m then
                ⌜Φ m⌝
              else (if (scheduled σ id) then True else VMProp_holds id (1/2)%Qp) -∗
              WP m @ id; ⊤ {{v, ⌜Φ v⌝ }})) →
  adequate ms σ ((λ φ, λ v _, φ v)<$> φs).
Proof.
  intros Hlen Hwp. apply adequate_alt. intros ms2 σ2 [n ?]%rtc_nsteps.
  eapply (wp_strong_adequacy Σ M); [|done]=> ?.
  iMod Hwp as "Hwp"; clear Hwp.
  iModIntro.
  iIntros (name_map_name).
  iDestruct ("Hwp" $! name_map_name) as (stateI) "Hwp".
  iExists stateI, ((λ φ, λ v, ⌜φ v⌝) <$> φs)%I.
  iMod "Hwp" as (Ps) "(%HPs & Hσ & Hwp)".
  iModIntro. iExists _; iSplit; first done; iFrame "Hσ".
  iSplitL.
  { rewrite !big_sepL2_fmap_r.
    iFrame. }
  iIntros (Hnstk) "Hsi Hpost".
  iApply fupd_mask_intro_discard; first set_solver.
  iSplit; last done.
  rewrite Forall2_lookup.
  iIntros (i).
  rewrite list_lookup_fmap.
  destruct (ms2 !! i) eqn:Hi.
  - destruct (lookup_lt_is_Some_2 φs i) as [φ Hφ].
    { rewrite -Hlen.
      erewrite nsteps_preserve_vms_length; last done.
      eapply lookup_lt_Some; done. }
    rewrite Hφ /=.
    rewrite /= big_sepL2_lookup; [|done|rewrite list_lookup_fmap Hφ; done].
    destruct (terminated m) eqn:Hmterm.
    + iDestruct "Hpost" as %?.
      iPureIntro. apply Some_Forall2.
      rewrite Hmterm; done.
    + iPureIntro. apply Some_Forall2.
      rewrite Hmterm; done.
  - rewrite (lookup_ge_None_2 φs i); last first.
    { rewrite -Hlen.
      erewrite nsteps_preserve_vms_length; last done.
      eapply lookup_ge_None_1; done. }
    iPureIntro. apply None_Forall2.
Qed.

Corollary wp_invariance Σ M `{!irisPreGS Σ} ms1 σ1 ms2 σ2 φ :
  (∀ `{Hinv : !invGS Σ},
     ⊢ |={⊤}=> ∀ name_map_name,
         ∃
         (stateI : nat → state M → iProp Σ),
         let _ : irisG M Σ := IrisG _ _ Hinv _ _ _ name_map_name stateI in
         |={⊤}=> ∃ (Ps : list (iProp Σ)),
       ⌜length Ps = length ms1⌝ ∗
       stateI (length ms1) σ1 ∗
       (([∗ list] id ↦ P ∈ Ps, VMProp id P 1) -∗
           [∗ list] id ↦ m ∈ ms1,
             if terminated m then
                True
              else (if (scheduled σ1 id) then True else VMProp_holds id (1/2)%Qp) -∗
              WP m @ id; ⊤ {{_, True }}) ∗
       (stateI (length ms2) σ2 -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc step (ms1, σ1) (ms2, σ2) →
  φ.
Proof.
  intros Hwp [n Hmss]%rtc_nsteps.
  assert (length ms1 = length ms2) as Hms1ms2len.
  { clear -Hmss.
    change ms1 with ((ms1, σ1).1).
    change ms2 with ((ms2, σ2).1).
    induction Hmss as [|? [] [] ??? <-]; first done.
    eapply step_length; done. }
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod Hwp as "Hwp".
  iModIntro.
  iIntros (name_map_name).
  iDestruct ("Hwp" $! name_map_name) as (stateI) "Hwp".
  iExists stateI, (replicate (length ms1) (λ _, True))%I.
  iMod "Hwp" as (Ps Hlen) "(Hσ & Hwp & Hφ)".
  iModIntro.
  iExists _; iSplit; first done.
  iFrame "Hσ".
  rewrite !big_sepL2_replicate_r; [|done|done].
  iFrame "Hwp".
  iIntros (?) "Hσ H /=".
  rewrite Hms1ms2len.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.
