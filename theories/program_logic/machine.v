From stdpp Require Import gmap.
From iris.algebra Require Export ofe.

Definition vmid := nat.

Section machine_mixin.
  Context {mode state : Type}.
  Context (terminated : mode → bool).

  Context (prim_step : mode → state → mode → state → Prop).

  Record MachineMixin := {
    mixin_terminated_stuck m σ m' σ' :
      prim_step m σ m' σ' → terminated m = false;
  }.
End machine_mixin.

Structure machine := Machine {
  mode : Type;
  state : Type;
  terminated : mode → bool;
  prim_step : mode → state → mode → state → Prop;
  scheduler : option (state → vmid → bool);
  machine_mixin :
    MachineMixin terminated prim_step
}.

Arguments Machine {_ _} _ _ _ _.
Arguments terminated {_} _.
Arguments prim_step {_} _ _ _ _.

Definition scheduled {M : machine} (σ : state M) (n : vmid) : bool :=
  match scheduler M with
  | Some P => P σ n
  | None => true
  end.

Canonical Structure stateO M := leibnizO (state M).
Canonical Structure modeO M := leibnizO (mode M).

Definition cfg (M : machine) := (list (mode M) * state M)%type.

Section machine.
  Context {M : machine}.
  Implicit Types σ : state M.
  Implicit Types m : mode M.

  Lemma terminated_stuck m σ m' σ' :
      prim_step m σ m' σ' → terminated m = false.
  Proof. apply machine_mixin. Qed.

  Definition reducible (m : mode M) (σ : state M) :=
    ∃ m' σ', prim_step m σ m' σ'.
  Definition irreducible (m : mode M) (σ : state M) :=
    ∀ m' σ', ¬prim_step m σ m' σ'.
  Definition stuck (m : mode M) (σ : state M) :=
    terminated m = false ∧ irreducible m σ.
  Definition not_stuck (m : mode M) (σ : state M) :=
    terminated m = true ∨ reducible m σ.

  Inductive step (ρ1 ρ2 : cfg M) : Prop :=
    | step_atomic m1 σ1 m2 σ2 ms1 ms2 :
       scheduled σ1 (length ms1) = true →
       ρ1 = (ms1 ++ m1 :: ms2, σ1) →
       ρ2 = (ms1 ++ m2 :: ms2, σ2) →
       prim_step m1 σ1 m2 σ2 →
       step ρ1 ρ2.
  Hint Constructors step : core.

  Lemma step_length ms1 σ1 ms2 σ2 :
    step (ms1, σ1) (ms2, σ2) → length ms1 = length ms2.
  Proof. inversion 1; simplify_eq. rewrite !app_length /=; done. Qed.

  Lemma not_reducible m σ : ¬reducible m σ ↔ irreducible m σ.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_terminated m σ : reducible m σ → terminated m = false.
  Proof. intros (?&?&?); eauto using terminated_stuck. Qed.
  Lemma terminated_irreducible m σ : terminated m = true → irreducible m σ.
  Proof. intros Heq1 ?? Heq2%terminated_stuck; rewrite Heq1 in Heq2; done. Qed.
  Lemma not_not_stuck m σ : ¬not_stuck m σ ↔ stuck m σ.
  Proof.
    rewrite /stuck /not_stuck -not_reducible.
    destruct (terminated m); split.
    - tauto.
    - intros [? ?]; done.
    - tauto.
    - intros [? ?] [|]; done.
  Qed.

  Lemma step_insert i t2 σ2 m m' σ3 :
    scheduled σ2 i = true →
    t2 !! i = Some m →
    prim_step m σ2 m' σ3 →
    step (t2, σ2) (<[i:=m']>t2, σ3).
  Proof.
    intros.
    edestruct (elem_of_list_split_length t2) as (t21&t22&?&?);
      first (by eauto using elem_of_list_lookup_2); simplify_eq.
    econstructor; eauto.
    rewrite insert_app_r_alt // Nat.sub_diag //.
  Qed.

  Lemma prim_step_not_stuck e σ e' σ' : prim_step e σ e' σ' → not_stuck e σ.
  Proof. rewrite /not_stuck /reducible. eauto 10. Qed.

  Class Terminated (e : mode M) :=
    _terminated : terminated e = true.

End machine.
