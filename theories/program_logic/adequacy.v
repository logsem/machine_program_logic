From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import wsat.
From machine_program_logic.program_logic Require Export weakestpre.
Import uPred.

Section adequacy.
Context `{!irisG M Σ}.
Implicit Types m : mode M.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : mode M → iProp Σ.
Implicit Types Φs : list (mode M → iProp Σ).

Notation wptp t Φs := ([∗ list] id ↦ e;Φ ∈ t;Φs, WP e @ id ; ⊤ {{ Φ }})%I.

Lemma wp_step id m1 σ1 m2 σ2 Φ :
  scheduled σ1 id →
  prim_step m1 σ1 m2 σ2 →
  state_interp σ1 -∗ WP m1 @ id; ⊤ {{ Φ }}
    ={⊤,∅}=∗ |={∅}▷=> |={∅,⊤}=>
    state_interp σ2 ∗ WP m2 @ id; ⊤ {{ Φ }}.
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (? ?) "Hσ H".
  rewrite (terminated_stuck m1 σ1 m2 σ2) //.
  iMod ("H" $! σ1 with "[//] Hσ") as "(_ & H)". iModIntro.
  iMod ("H" with "[//]") as "H".
  iModIntro; iNext; iModIntro.
  iMod "H" as "[$ $]"; done.
Qed.

Lemma wptp_step ms1 ms2 σ1 σ2 Φs :
  step (ms1,σ1) (ms2, σ2) →
  state_interp σ1 -∗
  wptp ms1 Φs -∗
  |={⊤,∅}=> |={∅}▷=> |={∅,⊤}=> state_interp σ2 ∗ wptp ms2 Φs.
Proof.
  iIntros (Hstep) "Hσ Ht".
  destruct Hstep as [m1' σ1' m2' σ2' t2' t3 Hstep]; simplify_eq/=.
  iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[? Ht]".
  iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht ?]".
  iMod (wp_step with "Hσ Ht") as ">H"; [by rewrite Nat.add_0_r|done|].
  iModIntro; iModIntro; iNext; iMod "H"; iModIntro.
  iMod "H" as "[$ ?]"; iFrame; done.
Qed.

Lemma wptp_steps n ms1 ms2 σ1 σ2 Φs :
  nsteps step n (ms1, σ1) (ms2, σ2) →
  state_interp σ1 -∗ wptp ms1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^n |={∅,⊤}=> state_interp σ2 ∗ wptp ms2 Φs.
Proof.
  revert ms1 ms2 σ1 σ2 Φs.
  induction n as [|n IH]=> em1 ms2 σ1 σ2 Φs /=.
  { inversion_clear 1; iIntros "? ?". iFrame.
    iMod (fupd_mask_subseteq ∅) as "H"; first done. by iFrame. }
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  iDestruct (wptp_step with "Hσ He") as ">H"; first eauto; simplify_eq.
  iModIntro. iApply step_fupd_fupd. iApply (step_fupd_wand with "H").
  iIntros ">[Hσ He]". iMod (IH with "Hσ He") as "IH"; first done. iModIntro.
  iApply (step_fupdN_wand with "IH"). iIntros ">[$ $]"; done.
Qed.

Lemma wp_not_stuck id m σ Φ :
  scheduled σ id →
  state_interp σ -∗ WP m @ id {{ Φ }} ={⊤}=∗ ⌜not_stuck m σ⌝.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck. iIntros (?) "Hσ H".
  destruct (terminated m) eqn:?; first by eauto.
  iSpecialize ("H" $! σ with "[//] Hσ"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wptp_strong_adequacy n Φs ms1 ms2 σ1 σ2:
  nsteps step n (ms1, σ1) (ms2, σ2) →
  state_interp σ1 -∗ wptp ms1 Φs
  ={⊤,∅}=∗ |={∅}▷=>^n |={∅,⊤}=>
    ⌜ ∀ i m2, scheduled σ2 i → ms2 !! i = Some m2 → not_stuck m2 σ2 ⌝ ∗
    state_interp σ2 ∗
    [∗ list] m;Φ ∈ ms2;Φs,
      from_option Φ True (if terminated m then Some m else None).
Proof.
  iIntros (Hstep) "Hσ He". iMod (wptp_steps with "Hσ He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as "(Hσ & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ i m2, scheduled σ2 i → ms2 !! i = Some m2 → not_stuck m2 σ2 ⌝%I
    (state_interp σ2 ∗ wptp ms2 Φs)%I
    with "[$Hσ $Ht]") as "(%&Hσ&Hwp)".
  { iIntros "(Hσ & Ht)" (i m' Hm'sch Hm').
    move: Hm' => /(elem_of_list_split_length _ _ _)[?[?[-> ?]]]; subst.
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ?) "[? Hwp]".
    iDestruct (big_sepL2_cons_inv_l with "Hwp") as (Φ Φs3 ->) "[Hwp ?]".
    rewrite Nat.add_0_r.
    iMod (wp_not_stuck with "Hσ Hwp") as "$"; auto. }
  iSplitR; first done. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Hwp").
  iIntros "!#" (? m Φ ??) "Hwp".
  destruct (terminated m) eqn:Hm2'; last done.
  simpl. iApply wp_terminated_inv'; done.
Qed.
End adequacy.

(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy Σ M `{!invPreG Σ} ms1 σ1 n ms2 σ2 φ :
  (∀ `{Hinv : !invG Σ},
    ⊢ |={⊤}=> ∃
         (stateI : state M → iProp Σ)
         (Φs : list (mode M → iProp Σ)),
       let _ : irisG M Σ := IrisG _ _ Hinv stateI in
       stateI σ1 ∗
       ([∗ list] id ↦ e;Φ ∈ ms1;Φs, WP e @ id; ⊤ {{ Φ }}) ∗
       ( (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ ∀ i m2, scheduled σ2 i → ms2 !! i = Some m2 → not_stuck m2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 -∗
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
  iMod Hwp as (stateI Φ) "(Hσ & Hwp & Hφ)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iMod (@wptp_strong_adequacy _ _ (IrisG _ _ Hinv stateI) _ with "Hσ Hwp")
    as "H"; first done.
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

Corollary wp_adequacy Σ M `{!invPreG Σ} ms σ φs :
  (∀ `{Hinv : !invG Σ},
     ⊢ |={⊤}=> ∃
         (stateI : state M → iProp Σ),
       let _ : irisG M Σ :=
           IrisG _ _ Hinv stateI
       in
       stateI σ ∗ ([∗ list] id ↦ e;Φ ∈ ms;φs, WP e @ id; ⊤ {{v, ⌜Φ v⌝ }})) →
  adequate ms σ ((λ φ, λ v _, φ v)<$> φs).
Proof.
  intros Hwp. apply adequate_alt. intros ms2 σ2 [n ?]%rtc_nsteps.
  eapply (wp_strong_adequacy Σ M); [|done]=> ?.
  iMod Hwp as (stateI) "[Hσ Hwp]".
  iExists stateI, ((λ φ, λ v, ⌜φ v⌝) <$> φs)%I.
  rewrite !big_sepL2_fmap_r.
  iIntros "{$Hσ $Hwp} !>" (?) "_ H".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_length with "H") as %Hlength.
  rewrite Forall2_lookup.
  iIntros (i).
  rewrite list_lookup_fmap.
  destruct (ms2 !! i) eqn:Hi.
  - destruct (lookup_lt_is_Some_2 φs i) as [φ Hφ].
    { rewrite -Hlength; eapply lookup_lt_Some; done. }
    rewrite Hφ /=.
    rewrite /= big_sepL2_lookup; [|done|done].
    destruct (terminated m) eqn:Hmterm.
    + iDestruct "H" as %?.
      iPureIntro. apply Some_Forall2.
      rewrite Hmterm; done.
    + iPureIntro. apply Some_Forall2.
      rewrite Hmterm; done.
  - rewrite (lookup_ge_None_2 φs i); last first.
    { rewrite -Hlength; eapply lookup_ge_None_1; done. }
    iPureIntro. apply None_Forall2.
Qed.

Corollary wp_invariance Σ M `{!invPreG Σ} ms1 σ1 ms2 σ2 φ :
  (∀ `{Hinv : !invG Σ},
     ⊢ |={⊤}=> ∃
         (stateI : state M → iProp Σ),
       let _ : irisG M Σ := IrisG _ _ Hinv stateI in
       stateI σ1 ∗ ([∗ list] id ↦ e ∈ ms1, WP e @ id; ⊤ {{v, True }}) ∗
       (stateI σ2 -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc step (ms1, σ1) (ms2, σ2) →
  φ.
Proof.
  intros Hwp [n Hmss]%rtc_nsteps.
  assert (length ms1 = length ms2).
  { clear -Hmss.
    change ms1 with ((ms1, σ1).1).
    change ms2 with ((ms2, σ2).1).
    induction Hmss as [|? [] [] ??? <-]; first done.
    eapply step_length; done. }
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod (Hwp _) as (stateI) "(Hσ & Hwp & Hφ)".
  iExists stateI, (replicate (length ms1) (λ _, True))%I.
  rewrite !big_sepL2_replicate_r; [|done|done].
  iIntros "{$Hσ $Hwp} !>" (?) "Hσ H /=".
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.
