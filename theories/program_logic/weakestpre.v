From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import cmra excl auth gmap agree frac_agree.
From iris.base_logic.lib Require Export fancy_updates saved_prop.
From machine_program_logic.program_logic Require Export machine.

Class irisG (M : machine) (Σ : gFunctors) := IrisG {
  iris_invG :> invGS Σ;
  irisG_saved_prop :> savedPropG Σ;
  irisG_prop_name :> inG Σ (authUR (optionUR (frac_agreeR gnameO)));
  irisG_name_map :> inG Σ (authUR (gmapUR nat (agreeR gnameO)));
  irisG_name_map_name : gname;
  (** The state interpretation is an invariant that should hold in between each
  step of reduction. *)
  state_interp : nat → state M → iProp Σ;
}.
Global Opaque iris_invG.

Section props.
  Context `{!irisG M Σ}.

  Definition VMProp (id : vmid) (P : iProp Σ) (q : frac) : iProp Σ :=
    ∃ γvmn γ, own irisG_name_map_name (◯ {[ id := to_agree γvmn]}) ∗
              own γvmn (◯ (Some (to_frac_agree q γ))) ∗ saved_prop_own γ P.

  Definition VMPropAuth (id : vmid) (P : iProp Σ) (q : frac) : iProp Σ :=
    ∃ γvmn γ, own irisG_name_map_name (◯ {[ id := to_agree γvmn]}) ∗
              own γvmn (● (Some (to_frac_agree q γ))) ∗ saved_prop_own γ P.

  Lemma VMProp_agree id P Q q q' : VMPropAuth id P q -∗ VMProp id Q q' -∗ ▷ (P ≡ Q).
  Proof.
    iDestruct 1 as (γvmn1 γ1) "(Hvmn1 & Hγ1 & #HP)".
    iDestruct 1 as (γvmn2 γ2) "(Hvmn2 & Hγ2 & #HQ)".
    iDestruct (own_valid_2 with "Hvmn1 Hvmn2") as %Hvalid%auth_frag_valid_1.
    specialize (Hvalid id).
    rewrite lookup_op !lookup_singleton -Some_op in Hvalid.
    apply to_agree_op_inv, leibniz_equiv in Hvalid as <-.
    iDestruct (own_valid_2 with "Hγ1 Hγ2") as %authv.
    apply auth_both_valid_discrete in authv.
    destruct authv as [authv1 authv2].
    apply option_included in authv1.
    destruct authv1 as [Contra | authv1]; first done.
    destruct authv1 as (a & b & Heq1 & Heq2 & Heq3).
    inversion Heq1 as [Heq1'].
    rewrite <-Heq1' in Heq3.
    inversion Heq2 as [Heq2'].
    rewrite <-Heq2' in Heq3.
    destruct Heq3 as [Heq3 | Hincl].
    - simplify_eq.
      inversion Heq3 as [Heq4 Heq5].
      simpl in *.
      apply to_agree_inj in Heq5.      
      simplify_eq.
      iApply saved_prop_agree; done.
    - apply frac_agree_included in Hincl.
      destruct Hincl as [_ Heq].
      iApply saved_prop_agree. iExact "HP".
      iEval (rewrite Heq) in "HQ".
      done.
  Qed.

  Lemma VMProp_agree' id P Q q q' : VMPropAuth id P q -∗ VMProp id Q q' -∗ ▷ P ≡ ▷ Q.
  Proof.
    iIntros "? ?".
    iApply later_equivI_prop_2.
    iApply (VMProp_agree with "[$] [$]").
  Qed.

  Lemma VMProp_update id P Q R : VMPropAuth id P 1 -∗ VMProp id Q 1 ==∗ VMPropAuth id R 1 ∗ VMProp id R 1.
  Proof.
    iDestruct 1 as (γvmn1 γ1) "(#Hvmn1 & Hγ1 & _)".
    iDestruct 1 as (γvmn2 γ2) "(#Hvmn2 & Hγ2 & _)".
    iDestruct (own_valid_2 with "Hvmn1 Hvmn2") as %Hvalid%auth_frag_valid_1.
    specialize (Hvalid id).
    rewrite lookup_op !lookup_singleton -Some_op in Hvalid.
    apply to_agree_op_inv, leibniz_equiv in Hvalid as <-.
    iDestruct (own_valid_2 with "Hγ1 Hγ2") as %authv.
    apply auth_both_valid_discrete in authv.
    destruct authv as [authv1 authv2].
    apply option_included in authv1.
    destruct authv1 as [Contra | authv1]; first done.
    destruct authv1 as (a & b & Heq1 & Heq2 & Heq3).
    inversion Heq1 as [Heq1'].
    rewrite <-Heq1' in Heq3.
    inversion Heq2 as [Heq2'].
    rewrite <-Heq2' in Heq3.    
    iMod (saved_prop_alloc R) as (γ) "#Hγ".
    iMod (own_update_2 _ _ _ (● (Some (to_frac_agree 1 γ)) ⋅ ◯ (Some (to_frac_agree 1 γ))) with "Hγ1 Hγ2") as "[Hγ1 Hγ2]".
    {
      apply auth_update, option_local_update.
      apply exclusive_local_update.
      done.
    }
    iModIntro; iSplitL "Hγ1"; iExists _, _; iFrame; iFrame "#".    
  Qed.

  Definition VMProp_holds (id : vmid) : iProp Σ := ∃ P q, ▷ P ∗ VMProp id P q.

End props.

Definition just_scheduled {M} (σ1 σ2 : state M) (id : vmid) : bool :=
  negb (scheduled σ1 id) && (scheduled σ2 id).

Definition just_scheduled_vms {M} (n : nat) (σ1 σ2 : state M) : list vmid :=
  filter (λ id, just_scheduled σ1 σ2 id = true) (seq 0 n).

(* The boolean in the postcondition is true if the vm was enabled before the step but *)
(* is disabled afterwards, unless it is terminated. *)

Definition sswp_def `{!irisG M Σ} (id : vmid) :
  coPset -d> mode M -d> ((bool * mode M) -d> iPropO Σ) -d> iPropO Σ := λ E m1 Φ,
  (if terminated m1 then |={E}=> Φ (false, m1) else
     ∀ n σ1, ⌜scheduled σ1 id⌝ -∗ state_interp n σ1 ={E,∅}=∗ ⌜reducible m1 σ1⌝ ∗
       ∀ m2 σ2,
         (∃ P q, VMPropAuth id P q) -∗
         ⌜prim_step m1 σ1 m2 σ2⌝ ={∅}=∗ ▷ |={∅,E}=>
         (∃ P q, VMPropAuth id P q) ∗ state_interp n σ2 ∗
         ([∗ list] vmid ∈ just_scheduled_vms n σ1 σ2, VMProp_holds vmid) ∗
         Φ (negb (scheduled σ2 id) && negb (terminated m2), m2))%I.

Definition sswp_aux : seal (@sswp_def). Proof. by eexists. Qed.
Definition sswp := sswp_aux.(unseal).
Arguments sswp {M Σ _}.
Lemma sswp_eq `{!irisG M Σ} : sswp = @sswp_def M Σ _.
Proof. rewrite -sswp_aux.(seal_eq) //. Qed.

Definition parwp_pre `{!irisG M Σ} (id : vmid)
    (parwp : coPset -d> mode M -d> (mode M -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> mode M -d> (mode M -d> iPropO Σ) -d> iPropO Σ := λ E m1 Φ,
  (|={E}=>
    (|={E}=> Φ m1) ∨
    ⌜terminated m1 = false⌝ ∧
    ∀ n σ1, ⌜scheduled σ1 id⌝ -∗ state_interp n σ1 ={E,∅}=∗ ⌜reducible m1 σ1⌝ ∗
      ∀ m2 σ2,
        (∃ P q, VMPropAuth id P q) -∗
        ⌜prim_step m1 σ1 m2 σ2⌝ ={∅}=∗ ▷ |={∅,E}=>
        (∃ P q, VMPropAuth id P q) ∗
        ([∗ list] vmid ∈ just_scheduled_vms n σ1 σ2, VMProp_holds vmid) ∗
        state_interp n σ2 ∗
        ((if scheduled σ2 id || terminated m2 then True else VMProp_holds id) -∗ parwp E m2 Φ))%I.

Local Instance parwp_pre_contractive `{!irisG M Σ} id : Contractive (parwp_pre id).
Proof.
  rewrite /parwp_pre=> n parwp parwp' Hparwp E m1 Φ /=.
  repeat (f_contractive || f_equiv); apply Hparwp.
Qed.

Definition parwp_def `{!irisG M Σ} (id: vmid) :
  coPset → mode M → (mode M → iProp Σ) → iProp Σ := fixpoint (parwp_pre id).
Definition parwp_aux : seal (@parwp_def). Proof. by eexists. Qed.
Definition parwp := parwp_aux.(unseal).
Arguments parwp {M Σ _}.
Lemma parwp_eq `{!irisG M Σ} : parwp = @parwp_def M Σ _.
Proof. rewrite -parwp_aux.(seal_eq) //. Qed.

Definition wp_pre `{!irisG M Σ} (id : vmid)
    (wp : coPset -d> mode M -d> (mode M -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> mode M -d> (mode M -d> iPropO Σ) -d> iPropO Σ := λ E m1 Φ,
  (if terminated m1 then |={E}=> Φ m1 else
     ∀ n σ1, ⌜scheduled σ1 id⌝ -∗ state_interp n σ1 ={E,∅}=∗ ⌜reducible m1 σ1⌝ ∗
       ∀ m2 σ2,
         (∃ P q, VMPropAuth id P q) -∗
         ⌜prim_step m1 σ1 m2 σ2⌝ ={∅}=∗ ▷ |={∅,E}=>
         (∃ P q, VMPropAuth id P q) ∗
         ([∗ list] vmid ∈ just_scheduled_vms n σ1 σ2, VMProp_holds vmid) ∗
         state_interp n σ2 ∗
         ((if scheduled σ2 id || terminated m2 then True else VMProp_holds id) -∗ wp E m2 Φ))%I.

Local Instance wp_pre_contractive `{!irisG M Σ} id : Contractive (wp_pre id).
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E m1 Φ /=.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{!irisG M Σ} (id: vmid) :
  coPset → mode M → (mode M → iProp Σ) → iProp Σ := fixpoint (wp_pre id).
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp := wp_aux.(unseal).
Arguments wp {M Σ _}.
Lemma wp_eq `{!irisG M Σ} : wp = @wp_def M Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

(** Notations for partial weakest preconditions *)
(** Notations without binder -- only parsing because they overlap with the
notations with binder. *)
Notation "'SSWP' m @ id ; E {{ Φ } }" := (sswp id E m Φ)
  (at level 20, m, Φ at level 200, only parsing) : bi_scope.
Notation "'SSWP' m @ id {{ Φ } }" := (sswp id ⊤ m Φ)
  (at level 20, m, Φ at level 200, only parsing) : bi_scope.

Notation "'PARWP' m @ id ; E {{ Φ } }" := (parwp id E m Φ)
  (at level 20, m, Φ at level 200, only parsing) : bi_scope.
Notation "'PARWP' m @ id {{ Φ } }" := (parwp id ⊤ m Φ)
  (at level 20, m, Φ at level 200, only parsing) : bi_scope.

Notation "'WP' m @ id ; E {{ Φ } }" := (wp id E m Φ)
  (at level 20, m, Φ at level 200, only parsing) : bi_scope.
Notation "'WP' m @ id {{ Φ } }" := (wp id ⊤ m Φ)
  (at level 20, m, Φ at level 200, only parsing) : bi_scope.

(** Notations with binder.  The indentation for the inner format block is chosen
such that *if* one has a single-character mask (e.g. [E]), the second line
should align with the binder(s) on the first line. *)
Notation "'SSWP' m @ id ; E {{ v , Q } }" := (sswp id E m (λ v, Q))
  (at level 20, m, Q at level 200,
   format "'[' 'SSWP'  m  '/' '[       ' @  id  ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'SSWP' m @ id {{ v , Q } }" := (sswp id ⊤ m (λ v, Q))
  (at level 20, m, Q at level 200,
   format "'[' 'SSWP'  m  '/' '[   ' @  id  {{  v ,  Q  } } ']' ']'") : bi_scope.

Notation "'PARWP' m @ id ; E {{ v , Q } }" := (parwp id E m (λ v, Q))
  (at level 20, m, Q at level 200,
   format "'[' 'PARWP'  m  '/' '[       ' @  id  ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'PARWP' m @ id {{ v , Q } }" := (parwp id ⊤ m (λ v, Q))
  (at level 20, m, Q at level 200,
   format "'[' 'PARWP'  m  '/' '[   ' @  id  {{  v ,  Q  } } ']' ']'") : bi_scope.

Notation "'WP' m @ id ; E {{ v , Q } }" := (wp id E m (λ v, Q))
  (at level 20, m, Q at level 200,
   format "'[' 'WP'  m  '/' '[       ' @  id  ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.
Notation "'WP' m @ id {{ v , Q } }" := (wp id ⊤ m (λ v, Q))
  (at level 20, m, Q at level 200,
   format "'[' 'WP'  m  '/' '[   ' @  id  {{  v ,  Q  } } ']' ']'") : bi_scope.

(* Texan triples - sswp *)
Notation "'{SS{{' P } } } e @ id ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ SSWP e @ id ; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {SS{{  P  } } }  '/  ' e  '/' @  id  ;  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{SS{{' P } } } e @ id {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ SSWP e @ id {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {SS{{  P  } } }  '/  ' e  '/' @  id  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.

Notation "'{SS{{' P } } } e @ id ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ SSWP e @ id ; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {SS{{  P  } } }  '/  ' e  '/' @  id  ;  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{SS{{' P } } } e @ id {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ SSWP e  @ id {{ Φ }})%I
    (at level 20,
     format "'[hv' {SS{{  P  } } }  '/  ' e  '/' @  id {{{  RET  pat ;  Q  } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{SS{{' P } } } e @ id ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ SSWP e @ id ; E {{ Φ }}) : stdpp_scope.
Notation "'{SS{{' P } } } e @ id {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ SSWP e @ id {{ Φ }}) : stdpp_scope.
Notation "'{SS{{' P } } } e @ id ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ SSWP e @ id ;  E {{ Φ }}) : stdpp_scope.
Notation "'{SS{{' P } } } e @ id {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ SSWP e @ id {{ Φ }}) : stdpp_scope.

(* Texan triples - parwp *)
Notation "'{PAR{{' P } } } e @ id ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ PARWP e @ id ; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {PAR{{  P  } } }  '/  ' e  '/' @  id  ;  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{PAR{{' P } } } e @ id {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ PARWP e @ id {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {PAR{{  P  } } }  '/  ' e  '/' @  id  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.

Notation "'{PAR{{' P } } } e @ id ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ PARWP e @ id ; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {PAR{{  P  } } }  '/  ' e  '/' @  id  ;  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{PAR{{' P } } } e @ id {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ PARWP e  @ id {{ Φ }})%I
    (at level 20,
     format "'[hv' {PAR{{  P  } } }  '/  ' e  '/' @  id {{{  RET  pat ;  Q  } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{PAR{{' P } } } e @ id ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ PARWP e @ id ; E {{ Φ }}) : stdpp_scope.
Notation "'{PAR{{' P } } } e @ id {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ PARWP e @ id {{ Φ }}) : stdpp_scope.
Notation "'{PAR{{' P } } } e @ id ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ PARWP e @ id ;  E {{ Φ }}) : stdpp_scope.
Notation "'{PAR{{' P } } } e @ id {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ PARWP e @ id {{ Φ }}) : stdpp_scope.

(* Texan triples - wp *)
Notation "'{{{' P } } } e @ id ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ id ; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  id  ;  E  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ id {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ id {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  id  {{{  x  ..  y ,  RET  pat ;  Q  } } } ']'") : bi_scope.

Notation "'{{{' P } } } e @ id ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ id ; E {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  id  ;  E  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.
Notation "'{{{' P } } } e @ id {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ id {{ Φ }})%I
    (at level 20,
     format "'[hv' {{{  P  } } }  '/  ' e  '/' @  id  {{{  RET  pat ;  Q  } } } ']'") : bi_scope.

(** Aliases for stdpp scope -- they inherit the levels and format from above. *)
Notation "'{{{' P } } } e @ id ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ id ; E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ id {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ id {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ id ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ id E {{ Φ }}) : stdpp_scope.
Notation "'{{{' P } } } e @ id {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ id {{ Φ }}) : stdpp_scope.

Section wp.
Context `{!irisG M Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : mode M → iProp Σ.
Implicit Types ξ : (bool * mode M) → iProp Σ.
Implicit Types m : mode M.
Implicit Types E : coPset.
Implicit Types id : vmid.

(* Weakest pre *)
Lemma wp_unfold id E m Φ :
  WP m @ id ; E {{ Φ }} ⊣⊢ wp_pre id (wp id) E m Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre id)). Qed.

Lemma parwp_unfold id E m Φ :
  PARWP m @ id; E {{ Φ }} ⊣⊢ parwp_pre id (parwp id) E m Φ.
Proof. rewrite parwp_eq. apply (fixpoint_unfold (parwp_pre id)). Qed.

Lemma wp_sswp id E m Φ :
  WP m @ id; E {{ Φ }} ⊣⊢
  SSWP m @ id; E {{bm, (if bm.1 then VMProp_holds id else True) -∗ WP bm.2 @ id; E {{ Φ }} }}.
Proof.
  rewrite wp_unfold sswp_eq /wp_pre /sswp_def.
  destruct (terminated m) eqn:Hm; simpl.
  - setoid_rewrite wp_unfold; rewrite /wp_pre Hm /=.
    iSplit.
    + iIntros ">?"; iModIntro; eauto.
    + iIntros ">H"; iApply "H"; done.
  - iSplit.
    + iIntros "H" (? ? ?) "Hsi".
      iMod ("H" with "[//] Hsi") as "[% H]".
      iModIntro; iSplit; first done.
      iIntros (? σ2) "HPr %".
      iMod ("H" with "[$] [//]") as "H".
      iModIntro.
      iNext.
      iMod "H" as "($&$&$&H)".
      iModIntro.
      destruct (scheduled σ2 id); destruct (terminated m2);
        simpl; iIntros "?"; iApply "H"; done.
    + iIntros "H" (? ? ?) "Hsi".
      iMod ("H" with "[//] Hsi") as "[% H]".
      iModIntro; iSplit; first done.
      iIntros (? σ2) "HPr %".
      iMod ("H" with "[$] [//]") as "H".
      iModIntro.
      iNext.
      iMod "H" as "($&$&$&H)".
      iModIntro.
      destruct (scheduled σ2 id); destruct (terminated m2);
        simpl; iIntros "?"; iApply "H"; done.
Qed.

Lemma wp_parwp id E m Φ :
  WP m @ id; E {{ Φ }} ⊣⊢ PARWP m @ id; E {{m', WP m' @ id; E {{ Φ }} }}.
Proof.
  iLöb as "IH" forall (m E Φ).
  rewrite wp_unfold parwp_unfold /wp_pre /parwp_pre.
  destruct (terminated m) eqn:Hm.
  - iClear "IH".
    iSplit.
    + iIntros "H". iLeft.
      setoid_rewrite wp_unfold; rewrite /wp_pre Hm fupd_idemp; done.
    + iIntros ">H".
      iDestruct "H" as "[H|H]".
      * setoid_rewrite wp_unfold; rewrite /wp_pre Hm fupd_idemp; done.
      * iDestruct "H"as "[% ?]"; done.
  - iSplit.
    + iIntros "H". iModIntro. iRight. iSplit; first done.
      iIntros (? σ1 Hsch) "Hσ1".
      iMod ("H" with "[//] Hσ1") as "[% H]".
      iModIntro. iSplit; first done.
      iIntros (m2 σ2) "HPr"; iIntros (Hstep).
      iMod ("H" with "[$] [//]") as "H".
      iModIntro; iNext.
      iMod "H" as "($&$&$&H)"; iModIntro.
      iIntros "His".
      iSpecialize ("H" with "His").
      iApply "IH"; done.
    + iIntros ">[H|H]".
      * iIntros (σ1 Hsch) "Hσ1".
        iMod "H".
        rewrite wp_unfold /wp_pre Hm.
        iApply "H"; done.
      * iDestruct "H" as "[_ H]".
        iIntros (? σ1 hsch) "Hσ1".
        iMod ("H" with "[//] Hσ1") as "[% H]".
        iModIntro. iSplit; first done.
        iIntros (m2 σ2) "HPr"; iIntros (Hstep).
        iMod ("H" with "[$] [//]") as "H".
        iModIntro; iNext.
        iMod "H" as "($&$&$&H)"; iModIntro.
        iIntros "His".
        iSpecialize ("H" with "His").
        iApply "IH"; done.
Qed.

Lemma parwp_sswp id E m Φ :
  SSWP m @ id; E {{bm, (if bm.1 then VMProp_holds id else True) -∗ PARWP bm.2 @ id; E {{ Φ }} }} ⊢
  PARWP m @ id; E {{ Φ }}.
Proof.
  rewrite sswp_eq parwp_unfold /sswp_def /parwp_pre.
  destruct (terminated m) eqn:Hm.
  - iIntros ">H".
    iModIntro; iLeft.
    rewrite parwp_unfold /parwp_pre /=.
    iMod ("H" with "[//]") as "[H|H]"; first done.
    rewrite Hm.
    iDestruct "H"as "[% ?]"; done.
  - iIntros "H"; iRight; iModIntro.
    iSplit; first done.
    iIntros (? ? ?) "Hsi".
    iMod ("H" with "[//] Hsi") as "[% H]".
    iModIntro; iSplit; first done.
    iIntros (? σ2) "HPr %".
    iMod ("H" with "[$] [//]") as "H".
    iModIntro; iNext.
    iMod "H" as "($&$&$&H)".
    iModIntro.
    iIntros "?".
    iApply "H".
    destruct (scheduled σ2 id); destruct (terminated m2); done.
Qed.

Global Instance sswp_ne id E m n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (sswp id E m).
Proof. rewrite sswp_eq /sswp_def; intros ?? Heq; repeat f_equiv. Qed.
Global Instance parwp_ne id E m n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (parwp id E m).
Proof.
  revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ HΦ.
  rewrite !parwp_unfold /parwp_pre.
  repeat ((f_contractive || f_equiv); try apply IH); eauto.
  eapply dist_le; eauto with lia.
Qed.
Global Instance wp_ne id E m n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp id E m).
Proof.
  revert m. induction (lt_wf n) as [n _ IH]=> m Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  repeat ((f_contractive || f_equiv); try apply IH); eauto.
  eapply dist_le; eauto with lia.
Qed.

Global Instance sswp_proper id E m :
  Proper (pointwise_relation _ (≡) ==> (≡)) (sswp id E m).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply sswp_ne=>v; apply equiv_dist.
Qed.
Global Instance parwp_proper id E m :
  Proper (pointwise_relation _ (≡) ==> (≡)) (parwp id E m).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply parwp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_proper id E m :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp id E m).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Global Instance sswp_contractive id E m n :
  TCEq (terminated m) false →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (sswp id E m).
Proof.
  intros He Φ Ψ HΦ. rewrite !sswp_eq /sswp_def He.
  repeat apply bi.forall_ne =>?.
  by repeat (f_contractive || f_equiv).
Qed.
Global Instance wp_contractive id E m n :
  TCEq (terminated m) false →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp id E m).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He.
  repeat apply bi.forall_ne =>?.
  by repeat (f_contractive || f_equiv).
Qed.

Lemma sswp_terminated' id E Φ m :
  terminated m = true → Φ m ⊢ SSWP m @ id ; E {{bm, ⌜bm.1 = false⌝ ∗ Φ bm.2}}.
Proof. iIntros (Hm) "HΦ". rewrite sswp_eq /sswp_def Hm /=; auto. Qed.
Lemma sswp_terminated_inv' id E ξ m :
  terminated m = true → SSWP m @ id ; E {{bm, ξ bm }} ={E}=∗ ξ (false, m).
Proof. intros Hm; rewrite sswp_eq /sswp_def Hm //. Qed.

Lemma parwp_finish id E Φ m : Φ m ⊢ PARWP m @ id ; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite parwp_unfold /parwp_pre; by iLeft. Qed.
Lemma parwp_terminated_inv' id E Φ m :
  terminated m = true → PARWP m @ id ; E {{ Φ }} ={E}=∗ Φ m.
Proof.
  intros Hm; rewrite parwp_unfold /parwp_pre Hm.
  iIntros ">[H|[% ?]]"; done.
Qed.

Lemma wp_terminated' id E Φ m : terminated m = true → Φ m ⊢ WP m @ id ; E {{ Φ }}.
Proof. iIntros (Hm) "HΦ". rewrite wp_unfold /wp_pre Hm. auto. Qed.
Lemma wp_terminated_inv' id E Φ m :
  terminated m = true → WP m @ id ; E {{ Φ }} ={E}=∗ Φ m.
Proof. by intros Hm; rewrite wp_unfold /wp_pre Hm. Qed.

Lemma sswp_strong_mono id E1 E2 m ξ Ψ :
  E1 ⊆ E2 →
  SSWP m @ id ; E1 {{ ξ }} -∗ (∀ bm, ξ bm ={E2}=∗ Ψ bm) -∗ SSWP m @ id ; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H Hξ".
  rewrite sswp_eq /sswp_def.
  destruct (terminated m) eqn:?.
  { iApply ("Hξ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (? σ1 Hsch) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[//] [$]") as "[% H]".
  iModIntro. iSplit; first done.
  iIntros (m2 σ2) "?"; iIntros (Hstep).
  iMod ("H" with "[$] [//]") as "H". iIntros "!> !>".
  iMod "H" as "(? & Hσ & ? & H)".
  iMod "Hclose" as "_".
  iMod ("Hξ" with "H"); iFrame; done.
Qed.

Lemma parwp_strong_mono id E1 E2 m Φ Ψ :
  E1 ⊆ E2 →
  PARWP m @ id ; E1 {{ Φ }} -∗ (∀ k, Φ k ={E2}=∗ Ψ k) -∗ PARWP m @ id ; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ".
  iLöb as "IH" forall (m E1 E2 HE Φ Ψ).
  rewrite !parwp_unfold /parwp_pre.
  iApply (fupd_mask_mono E1 _); first done.
  iMod "H"; iModIntro.
  iDestruct "H" as "[H|[% H]]".
  { iLeft. iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iRight; iSplit; first done.
  iIntros (? σ1 Hsch) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[//] [$]") as "[% H]".
  iModIntro. iSplit; first done.
  iIntros (m2 σ2) "?"; iIntros (Hstep).
  iMod ("H" with "[$] [//]") as "H". iIntros "!> !>".
  iMod "H" as "($ & $ & $ & H)".
  iMod "Hclose" as "_". iModIntro.
  iIntros "His".
  iSpecialize ("H" with "His").
  iApply ("IH" with "[//] H HΦ").
Qed.

Lemma wp_strong_mono id E1 E2 m Φ Ψ :
  E1 ⊆ E2 →
  WP m @ id; E1 {{ Φ }} -∗ (∀ k, Φ k ={E2}=∗ Ψ k) -∗ WP m @ id; E2 {{ Ψ }}.
Proof.
  iIntros (HE) "H HΦ". iLöb as "IH" forall (m E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre.
  destruct (terminated m) eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (? σ1 Hsch) "Hσ".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[//] [$]") as "[% H]".
  iModIntro. iSplit; first done.
  iIntros (m2 σ2) "?"; iIntros (Hstep).
  iMod ("H" with "[$] [//]") as "H". iIntros "!> !>".
  iMod "H" as "($ & $ & $ & H)".
  iMod "Hclose" as "_". iModIntro.
  iIntros "His".
  iSpecialize ("H" with "His").
  iApply ("IH" with "[//] H HΦ").
Qed.

Lemma fupd_sswp id E m ξ :
  (|={E}=> SSWP m @ id ; E {{ ξ }}) ⊢ SSWP m @ id; E {{ ξ}}.
Proof.
  rewrite sswp_eq /sswp_def. iIntros "H".
  destruct (terminated m) eqn:?.
  { by iMod "H". }
  iIntros (? σ1) "Hσ1". iMod "H".
  iApply ("H" with "Hσ1"); done.
Qed.
Lemma sswp_fupd id E m ξ :
  SSWP m @ id; E {{ bm, |={E}=> ξ bm }} ⊢ SSWP m @ id; E {{ ξ }}.
Proof. iIntros "H". iApply (sswp_strong_mono id E with "H"); auto. Qed.

Lemma fupd_parwp id E m Φ :
  (|={E}=> PARWP m @ id ; E {{ Φ }}) ⊢ PARWP m @ id; E {{ Φ }}.
Proof. rewrite parwp_unfold /parwp_pre. iIntros ">H"; done. Qed.

Lemma parwp_parwp id E m Φ :
  PARWP m @ id; E {{m', PARWP m' @ id; E {{ Φ }} }} ⊢ PARWP m @ id; E {{ Φ }}.
Proof.
  iLöb as "IH" forall (m E Φ).
  rewrite parwp_unfold /parwp_pre.
  iIntros "H".
  iApply fupd_parwp.
  iMod "H" as "[H|H]".
  - by iMod "H".
  - iDestruct "H" as "[% H]".
    rewrite parwp_unfold.
    rewrite /parwp_pre /parwp_def.
    iModIntro.
    iRight.
    iModIntro.
    iSplit; [done|].
    iIntros (? σ1) "%sch".
    iIntros "sti".
    iSpecialize ("H" $! _ σ1 sch with "sti").
    iMod "H".
    iDestruct "H" as "(red & H)".
    iModIntro.
    iSplit; first done.
    iIntros (m2 σ2) "HPr prims".
    iSpecialize ("H" $! m2 σ2 with "HPr prims").
    iMod "H".
    iModIntro.
    iModIntro.
    iMod "H".
    iDestruct "H" as "($ & sti' & $ & par)".
    iModIntro.
    iSplitL "sti'"; first done.
    iIntros "His".
    iSpecialize ("par" with "His").
    iApply ("IH" $! m2 E Φ with "par").
Qed.

Lemma parwp_fupd id E m Φ :
  PARWP m @ id; E {{ k, |={E}=> Φ k }} ⊢ PARWP m @ id; E {{ Φ }}.
Proof. iIntros "H". iApply (parwp_strong_mono id E with "H"); auto. Qed.

Lemma fupd_wp id E m Φ : (|={E}=> WP m @ id; E {{ Φ }}) ⊢ WP m @ id; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (terminated m) eqn:?.
  { by iMod "H". }
  iIntros (? σ1) "Hσ1". iMod "H".
  iApply ("H" with "Hσ1"); done.
Qed.
Lemma wp_fupd id E m Φ : WP m @ id; E {{ k, |={E}=> Φ k }} ⊢ WP m @ id; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono id E with "H"); auto. Qed.

Lemma sswp_fupd_around id E1 E2 m ξ :
  (|={E1,E2}=> SSWP m @ id; E2 {{ bm, |={E2,E1}=> ξ bm }}) ⊢ SSWP m @ id; E1 {{ ξ }}.
Proof.
  iIntros "H".
  rewrite sswp_eq /sswp_def.
  destruct (terminated m).
  { by iDestruct "H" as ">>> $". }
  iIntros (? σ1 Hsch) "Hσ1".
  iMod "H". iMod ("H" with "[//] Hσ1") as "[% H]".
  iModIntro; iSplit; first done.
  iIntros (m2 σ2) "HPr"; iIntros (Hstep).
  iMod ("H" with "[$] [//]") as "H".
  iModIntro. iNext.
  iMod "H" as "($&$&$&>$)"; done.
Qed.

Lemma sswp_step_fupd id E1 E2 m P ξ :
  TCEq (terminated m) false →
  (|={E1}[E2]▷=> P) -∗
  SSWP m @ id; E2 {{ bm, P ={E1}=∗ ξ bm }} -∗
  SSWP m @ id; E1 {{ ξ }}.
Proof.
  rewrite sswp_eq /sswp_def. iIntros (->) "HP H".
  iIntros (? σ1 Hsch) "Hσ1".
  iMod "HP".
  iMod ("H" with "[//] Hσ1") as "[% H]".
  iModIntro; iSplit; first done.
  iIntros (σ2 m2) "HPr"; iIntros (Hstep).
  iMod ("H" with "[$] [//]") as "H".
  iModIntro; iNext.
  iMod "H" as "($&$&$&H)".
  iMod "HP"; iApply "H"; done.
Qed.

Lemma wp_step_fupd id E1 E2 m P Φ :
  TCEq (terminated m) false → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗
  WP m @ id; E2 {{ k, P ={E1}=∗ Φ k }} -∗
  WP m @ id; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HP H".
  iIntros (? σ1 Hsch) "Hσ1".
  iMod "HP".
  iMod ("H" with "[//] Hσ1") as "[% H]".
  iModIntro; iSplit; first done.
  iIntros (σ2 m2) "HPr"; iIntros (Hstep).
  iMod ("H" with "[$] [//]") as "H".
  iModIntro; iNext.
  iMod "H" as "($&$&$&H)".
  iMod "HP".
  iModIntro.
  iIntros "His".
  iSpecialize ("H" with "His").
  iApply (wp_strong_mono with "H"); first done.
  iIntros (k) "H"; iApply "H"; done.
Qed.

(** * Derived rules *)
Lemma sswp_mono id E m ξ Ψ :
  (∀ bm, ξ bm ⊢ Ψ bm) → SSWP m @ id; E {{ ξ }} ⊢ SSWP m @ id; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (sswp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma parwp_mono id E m Φ Ψ :
  (∀ k, Φ k ⊢ Ψ k) → PARWP m @ id; E {{ Φ }} ⊢ PARWP m @ id; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (parwp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_mono id E m Φ Ψ :
  (∀ k, Φ k ⊢ Ψ k) → WP m @ id; E {{ Φ }} ⊢ WP m @ id; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma sswp_mask_mono id E1 E2 m ξ :
  E1 ⊆ E2 → SSWP m @ id; E1 {{ ξ }} ⊢ SSWP m @ id; E2 {{ ξ }}.
Proof. iIntros (?) "H"; iApply (sswp_strong_mono with "H"); auto. Qed.
Lemma parwp_mask_mono id E1 E2 m Φ :
  E1 ⊆ E2 → PARWP m @ id; E1 {{ Φ }} ⊢ PARWP m @ id; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (parwp_strong_mono with "H"); auto. Qed.
Lemma wp_mask_mono id E1 E2 m Φ :
  E1 ⊆ E2 → WP m @ id; E1 {{ Φ }} ⊢ WP m @ id; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance sswp_mono' id E m :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (sswp id E m).
Proof. by intros Φ Φ' ?; apply sswp_mono. Qed.
Global Instance parwp_mono' id E m :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (parwp id E m).
Proof. by intros Φ Φ' ?; apply parwp_mono. Qed.
Global Instance wp_mono' id E m :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp id E m).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance sswp_flip_mono' id E m :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (sswp id E m).
Proof. by intros Φ Φ' ?; apply sswp_mono. Qed.
Global Instance parwp_flip_mono' id E m :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (parwp id E m).
Proof. by intros Φ Φ' ?; apply parwp_mono. Qed.
Global Instance wp_flip_mono' id E m :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp id E m).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma sswp_terminated id E Φ m :
  Terminated m → Φ m ⊢ SSWP m @ id; E {{ bm, ⌜bm.1 = false⌝ ∗ Φ bm.2 }}.
Proof. apply sswp_terminated'. Qed.
Lemma wp_terminated id E Φ m : Terminated m → Φ m ⊢ WP m @ id; E {{ Φ }}.
Proof. apply wp_terminated'. Qed.
Lemma sswp_terminated_fupd' id E Φ m :
  Terminated m → (|={E}=> Φ m) ⊢ SSWP m @ id; E {{ bm, ⌜bm.1 = false⌝ ∗ Φ bm.2 }}.
Proof. intros ?; rewrite -fupd_sswp -sswp_terminated'; done. Qed.
Lemma parwp_finish_fupd id E Φ m :
  (|={E}=> Φ m) ⊢ PARWP m @ id; E {{ Φ }}.
Proof. by intros; rewrite -parwp_fupd -parwp_finish. Qed.
Lemma wp_terminated_fupd' id E Φ m :
  Terminated m → (|={E}=> Φ m) ⊢ WP m @ id; E {{ Φ }}.
Proof. by intros; rewrite -wp_fupd -wp_terminated'. Qed.
Lemma sswp_terminated_fupd id E Φ m `{!Terminated m} :
  (|={E}=> Φ m) ⊢ SSWP m @ id; E {{ bm, ⌜bm.1 = false⌝ ∗ Φ bm.2 }}.
Proof. intros; rewrite -fupd_sswp -sswp_terminated //. Qed.
Lemma wp_terminated_fupd id E Φ m `{!Terminated m} :
  (|={E}=> Φ m) ⊢ WP m @ id; E {{ Φ }}.
Proof. intros; rewrite -wp_fupd -wp_terminated //. Qed.
Lemma sswp_terminated_inv id E ξ m :
  Terminated m → SSWP m @ id; E {{ ξ }} ={E}=∗ ξ (false, m).
Proof. intros ?; rewrite sswp_terminated_inv'; auto. Qed.
Lemma parwp_terminated_inv id E Φ m :
  Terminated m → PARWP m @ id; E {{ Φ }} ={E}=∗ Φ m.
Proof. by apply parwp_terminated_inv'. Qed.
Lemma wp_terminated_inv id E Φ m :
  Terminated m → WP m @ id; E {{ Φ }} ={E}=∗ Φ m.
Proof. by apply wp_terminated_inv'. Qed.

Lemma sswp_frame_l id E m ξ R :
  R ∗ SSWP m @ id; E {{ ξ }} ⊢ SSWP m @ id; E {{ k, R ∗ ξ k }}.
Proof. iIntros "[? H]". iApply (sswp_strong_mono with "H"); auto with iFrame. Qed.
Lemma parwp_frame_l id E m Φ R :
  R ∗ PARWP m @ id; E {{ Φ }} ⊢ PARWP m @ id; E {{ k, R ∗ Φ k }}.
Proof. iIntros "[? H]". iApply (parwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_l id E m Φ R :
  R ∗ WP m @ id; E {{ Φ }} ⊢ WP m @ id; E {{ k, R ∗ Φ k }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma sswp_frame_r id E m ξ R :
  SSWP m @ id; E {{ ξ }} ∗ R ⊢ SSWP m @ id; E {{ k, ξ k ∗ R }}.
Proof. iIntros "[H ?]". iApply (sswp_strong_mono with "H"); auto with iFrame. Qed.
Lemma parwp_frame_r id E m Φ R :
  PARWP m @ id; E {{ Φ }} ∗ R ⊢ PARWP m @ id; E {{ k, Φ k ∗ R }}.
Proof. iIntros "[H ?]". iApply (parwp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r id E m Φ R :
  WP m @ id; E {{ Φ }} ∗ R ⊢ WP m @ id; E {{ k, Φ k ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma sswp_frame_step_l id E1 E2 m ξ R :
  TCEq (terminated m) false → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ SSWP m @ id; E2 {{ ξ }} ⊢ SSWP m @ id; E1 {{ k, R ∗ ξ k }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (sswp_step_fupd with "Hu"); try done.
  iApply (sswp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_l id E1 E2 m Φ R :
  TCEq (terminated m) false → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP m @ id; E2 {{ Φ }} ⊢ WP m @ id; E1 {{ k, R ∗ Φ k }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma sswp_frame_step_r id E1 E2 m ξ R :
  TCEq (terminated m) false → E2 ⊆ E1 →
  SSWP m @ id; E2 {{ ξ }} ∗ (|={E1}[E2]▷=> R) ⊢ SSWP m @ id; E1 {{ k, ξ k ∗ R }}.
Proof.
  rewrite [(SSWP _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply sswp_frame_step_l.
Qed.
Lemma wp_frame_step_r id E1 E2 m Φ R :
  TCEq (terminated m) false → E2 ⊆ E1 →
  WP m @ id; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP m @ id; E1 {{ k, Φ k ∗ R }}.
Proof.
  rewrite [(WP _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma sswp_frame_step_l' id E m ξ R :
  TCEq (terminated m) false →
  ▷ R ∗ SSWP m @ id; E {{ ξ }} ⊢ SSWP m @ id; E {{ k, R ∗ ξ k }}.
Proof. iIntros (?) "[??]". iApply (sswp_frame_step_l id E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_l' id E m Φ R :
  TCEq (terminated m) false →
  ▷ R ∗ WP m @ id; E {{ Φ }} ⊢ WP m @ id; E {{ k, R ∗ Φ k }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l id E E); try iFrame; eauto. Qed.
Lemma sswp_frame_step_r' id E m ξ R :
  TCEq (terminated m) false →
  SSWP m @ id; E {{ ξ }} ∗ ▷ R ⊢ SSWP m @ id; E {{ k, ξ k ∗ R }}.
Proof. iIntros (?) "[??]". iApply (sswp_frame_step_r id E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' id E m Φ R :
  TCEq (terminated m) false →
  WP m @ id; E {{ Φ }} ∗ ▷ R ⊢ WP m @ id; E {{ k, Φ k ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r id E E); try iFrame; eauto. Qed.

Lemma sswp_wand id E m ξ Ψ :
  SSWP m @ id; E {{ ξ }} -∗ (∀ k, ξ k -∗ Ψ k) -∗ SSWP m @ id; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (sswp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma parwp_wand id E m Φ Ψ :
  PARWP m @ id; E {{ Φ }} -∗ (∀ k, Φ k -∗ Ψ k) -∗ PARWP m @ id; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (parwp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand id E m Φ Ψ :
  WP m @ id; E {{ Φ }} -∗ (∀ k, Φ k -∗ Ψ k) -∗ WP m @ id; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma sswp_wand_l id E m ξ Ψ :
  (∀ k, ξ k -∗ Ψ k) ∗ SSWP m @ id; E {{ ξ }} ⊢ SSWP m @ id; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (sswp_wand with "Hwp H"). Qed.
Lemma parwp_wand_l id E m Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ PARWP m @ id; E {{ Φ }} ⊢ PARWP m @ id; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (parwp_wand with "Hwp H"). Qed.
Lemma wp_wand_l id E m Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP m @ id; E {{ Φ }} ⊢ WP m @ id; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma sswp_wand_r id E m ξ Ψ :
  SSWP m @ id; E {{ ξ }} ∗ (∀ v, ξ v -∗ Ψ v) ⊢ SSWP m @ id; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (sswp_wand with "Hwp H"). Qed.
Lemma parwp_wand_r id E m Φ Ψ :
  PARWP m @ id; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ PARWP m @ id; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (parwp_wand with "Hwp H"). Qed.
Lemma wp_wand_r id E m Φ Ψ :
  WP m @ id; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP m @ id; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma sswp_frame_wand_l id E m Q ξ :
  Q ∗ SSWP m @ id; E {{ v, Q -∗ ξ v }} -∗ SSWP m @ id; E {{ ξ }}.
Proof.
  iIntros "[HQ HWP]". iApply (sswp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
Lemma parwp_frame_wand_l id E m Q Φ :
  Q ∗ PARWP m @ id; E {{ v, Q -∗ Φ v }} -∗ PARWP m @ id; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (parwp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.
Lemma wp_frame_wand_l id E m Q Φ :
  Q ∗ WP m @ id; E {{ v, Q -∗ Φ v }} -∗ WP m @ id; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisG M Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : mode M → iProp Σ.
  Implicit Types E : coPset.
  Implicit Types id : vmid.

  Global Instance frame_sswp p id E m R ξ Ψ :
    (∀ k, Frame p R (ξ k) (Ψ k)) →
    Frame p R (SSWP m @ id; E {{ ξ }}) (SSWP m @ id; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite sswp_frame_l. apply sswp_mono, HR. Qed.

  Global Instance frame_parwp p id E m R Φ Ψ :
    (∀ k, Frame p R (Φ k) (Ψ k)) →
    Frame p R (PARWP m @ id; E {{ Φ }}) (PARWP m @ id; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite parwp_frame_l. apply parwp_mono, HR. Qed.

  Global Instance frame_wp p id E m R Φ Ψ :
    (∀ k, Frame p R (Φ k) (Ψ k)) →
    Frame p R (WP m @ id; E {{ Φ }}) (WP m @ id; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_sswp id E m ξ : IsExcept0 (SSWP m @ id; E {{ ξ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_sswp -except_0_fupd -fupd_intro. Qed.

  Global Instance is_except_0_parwp id E m Φ : IsExcept0 (PARWP m @ id; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_parwp -except_0_fupd -fupd_intro. Qed.

  Global Instance is_except_0_wp id E m Φ : IsExcept0 (WP m @ id; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_sswp p id E m P ξ :
    ElimModal True p false (|==> P) P (SSWP m @ id; E {{ ξ }}) (SSWP m @ id; E {{ ξ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_sswp.
  Qed.

  Global Instance elim_modal_bupd_parwp p id E m P Φ :
    ElimModal True p false (|==> P) P (PARWP m @ id; E {{ Φ }}) (PARWP m @ id; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_parwp.
  Qed.

  Global Instance elim_modal_bupd_wp p id E m P Φ :
    ElimModal True p false (|==> P) P (WP m @ id; E {{ Φ }}) (WP m @ id; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_sswp p id E m P ξ :
    ElimModal True p false (|={E}=> P) P (SSWP m @ id; E {{ ξ }}) (SSWP m @ id; E {{ ξ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_sswp.
  Qed.

  Global Instance elim_modal_fupd_parwp p id E m P Φ :
    ElimModal True p false (|={E}=> P) P (PARWP m @ id; E {{ Φ }}) (PARWP m @ id; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_parwp.
  Qed.

  Global Instance elim_modal_fupd_wp p id E m P Φ :
    ElimModal True p false (|={E}=> P) P (WP m @ id; E {{ Φ }}) (WP m @ id; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_sswp_around p id E1 E2 m P ξ :
    ElimModal True p false (|={E1,E2}=> P) P
            (SSWP m @ id; E1 {{ ξ }}) (SSWP m @ id; E2 {{ v, |={E2,E1}=> ξ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r sswp_fupd_around.
  Qed.

  Global Instance add_modal_fupd_sswp id E m P ξ :
    AddModal (|={E}=> P) P (SSWP m @ id; E {{ ξ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_sswp. Qed.

  Global Instance add_modal_fupd_parwp id E m P Φ :
    AddModal (|={E}=> P) P (PARWP m @ id; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_parwp. Qed.

  Global Instance add_modal_fupd_wp id E m P Φ :
    AddModal (|={E}=> P) P (WP m @ id; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_sswp {X} id E1 E2 α β γ m ξ :
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1)
            α β γ (SSWP m @ id; E1 {{ ξ }})
            (λ x, SSWP m @ id; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? ξ v) }})%I.
  Proof.
    intros _.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (sswp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_parwp_nonatomic {X} id E α β γ m Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (PARWP m @ id; E {{ Φ }})
            (λ x, PARWP m @ id; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply parwp_fupd.
    iApply (parwp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} id E α β γ m Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP m @ id; E {{ Φ }})
            (λ x, WP m @ id; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

End proofmode_classes.
