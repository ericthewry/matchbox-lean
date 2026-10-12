import Std

open Classical

namespace Proofs

abbrev Var := String
abbrev TableVar := String
abbrev Value := Int

abbrev Valuation := Var → Option Value
abbrev Formula := Valuation → Prop

inductive Action where
  | atom : String → Action
  | pair : Action → Action → Action
deriving DecidableEq, Repr

abbrev RelSem := Valuation → (Action × Valuation) → Prop

def Defined (f : RelSem) (ν : Valuation) : Prop := ∃ out, f ν out

def agreesOn (xs : List Var) (ν₁ ν₂ : Valuation) : Prop :=
  ∀ x, x ∈ xs → ν₁ x = ν₂ x

def supportWithin (ys : List Var) (ν : Valuation) : Prop :=
  ∀ x, ν x ≠ none → x ∈ ys

def mergeVal (ν₁ ν₂ : Valuation) : Valuation :=
  fun x =>
    match ν₁ x with
    | some v => some v
    | none => ν₂ x

theorem agreesOn_nil {ν₁ ν₂ : Valuation} : agreesOn [] ν₁ ν₂ := by
  intro x hx
  cases hx

theorem agreesOn_of_mem_append_left {xs ys : List Var} {ν₁ ν₂ : Valuation}
    (h : agreesOn (xs ++ ys) ν₁ ν₂) : agreesOn xs ν₁ ν₂ := by
  intro x hx
  exact h x (List.mem_append.mpr <| Or.inl hx)

theorem agreesOn_of_mem_append_right {xs ys : List Var} {ν₁ ν₂ : Valuation}
    (h : agreesOn (xs ++ ys) ν₁ ν₂) : agreesOn ys ν₁ ν₂ := by
  intro x hx
  exact h x (List.mem_append.mpr <| Or.inr hx)

theorem supportWithin_merge {ys₁ ys₂ : List Var} {ν₁ ν₂ : Valuation}
    (h₁ : supportWithin ys₁ ν₁) (h₂ : supportWithin ys₂ ν₂) :
    supportWithin (ys₁ ++ ys₂) (mergeVal ν₁ ν₂) := by
  intro x hx
  by_cases h : ν₁ x = none
  · have hx₂ : ν₂ x ≠ none := by
      simpa [mergeVal, h] using hx
    exact List.mem_append.mpr <| Or.inr <| h₂ x hx₂
  · have hx₁ : ν₁ x ≠ none := h
    exact List.mem_append.mpr <| Or.inl <| h₁ x hx₁

structure GFD where
  xs : List Var
  guard : Formula
  ys : List Var
  post : Formula

def Satisfies (f : RelSem) (Φ : GFD) : Prop :=
  ∀ ⦃ν₁ ν₂ : Valuation⦄,
    Φ.guard ν₁ →
    Φ.guard ν₂ →
    agreesOn Φ.xs ν₁ ν₂ →
    Defined f ν₁ ∧
    Defined f ν₂ ∧
    (∀ out, f ν₁ out → supportWithin Φ.ys out.2 ∧ Φ.post out.2) ∧
    (∀ out, f ν₂ out → supportWithin Φ.ys out.2 ∧ Φ.post out.2) ∧
    ∀ out₁ out₂, f ν₁ out₁ → f ν₂ out₂ → out₁ = out₂

inductive Program where
  | lit : RelSem → Program
  | var : TableVar → Program
  | filter : Formula → Program → Program
  | seq : Program → Program → Program
  | join : Program → Program → Program
  | pref : Program → Program → Program

def denote (σ : TableVar → RelSem) : Program → RelSem
  | Program.lit T => T
  | Program.var t => σ t
  | Program.filter φ C => fun ν out => φ ν ∧ denote σ C ν out
  | Program.seq C₁ C₂ => fun ν out =>
      ∃ mid : Action × Valuation, denote σ C₁ ν mid ∧ denote σ C₂ mid.2 out
  | Program.join C₁ C₂ => fun ν out =>
      ∃ a₁ a₂ ν₁ ν₂,
        denote σ C₁ ν (a₁, ν₁) ∧
        denote σ C₂ ν (a₂, ν₂) ∧
        out = (Action.pair a₁ a₂, mergeVal ν₁ ν₂)
  | Program.pref C₁ C₂ => fun ν out =>
      denote σ C₁ ν out ∨ (¬ Defined (denote σ C₁) ν ∧ denote σ C₂ ν out)

def EnvModelsDom (σ : TableVar → RelSem) (Δ : TableVar → Formula) : Prop :=
  ∀ t ν, Defined (σ t) ν → Δ t ν

def EnvModelsFD (σ : TableVar → RelSem) (Γ : TableVar → List GFD) : Prop :=
  ∀ t Φ, Φ ∈ Γ t → Satisfies (σ t) Φ

inductive DomCheck (Δ : TableVar → Formula) : Program → Formula → Prop where
  | var {t} :
      DomCheck Δ (Program.var t) (Δ t)
  | lit {T φ} :
      (∀ ν, Defined T ν → φ ν) →
      DomCheck Δ (Program.lit T) φ
  | filter {C φ ϑ} :
      DomCheck Δ C φ →
      DomCheck Δ (Program.filter ϑ C) (fun ν => φ ν ∧ ϑ ν)
  | seq {C₁ C₂ φ} :
      DomCheck Δ C₁ φ →
      DomCheck Δ (Program.seq C₁ C₂) φ
  | join {C₁ C₂ φ₁ φ₂} :
      DomCheck Δ C₁ φ₁ →
      DomCheck Δ C₂ φ₂ →
      DomCheck Δ (Program.join C₁ C₂) (fun ν => φ₁ ν ∧ φ₂ ν)
  | pref {C₁ C₂ φ₁ φ₂} :
      DomCheck Δ C₁ φ₁ →
      DomCheck Δ C₂ φ₂ →
      DomCheck Δ (Program.pref C₁ C₂) (fun ν => φ₁ ν ∨ φ₂ ν)

inductive FDCheck (Γ : TableVar → List GFD) (Δ : TableVar → Formula) : Program → GFD → Prop where
  | ctx {t Φ} :
      Φ ∈ Γ t →
      FDCheck Γ Δ (Program.var t) Φ
  | lit {T Φ} :
      Satisfies T Φ →
      FDCheck Γ Δ (Program.lit T) Φ
  | refine {C Φ ϑ} :
      FDCheck Γ Δ C Φ →
      FDCheck Γ Δ (Program.filter ϑ C) { Φ with guard := fun ν => Φ.guard ν ∧ ϑ ν }
  | compose {C₁ C₂ xs ys zs φ ϑ ψ} :
      FDCheck Γ Δ C₁ ⟨xs, φ, ys, ϑ⟩ →
      FDCheck Γ Δ C₂ ⟨ys, ϑ, zs, ψ⟩ →
      FDCheck Γ Δ (Program.seq C₁ C₂) ⟨xs, φ, zs, ψ⟩
  | join {C₁ C₂ xs₁ xs₂ ys₁ ys₂ φ₁ φ₂ ψ₁ ψ₂} :
      FDCheck Γ Δ C₁ ⟨xs₁, φ₁, ys₁, ψ₁⟩ →
      FDCheck Γ Δ C₂ ⟨xs₂, φ₂, ys₂, ψ₂⟩ →
      FDCheck Γ Δ (Program.join C₁ C₂)
        ⟨xs₁ ++ xs₂, (fun ν => φ₁ ν ∧ φ₂ ν), ys₁ ++ ys₂,
          (fun ν => ∃ ν₁ ν₂,
            ν = mergeVal ν₁ ν₂ ∧ ψ₁ ν₁ ∧ ψ₂ ν₂ ∧
              supportWithin ys₁ ν₁ ∧ supportWithin ys₂ ν₂)⟩
  | prefLeft {C₁ C₂ xs ys φ ψ ϑ} :
      FDCheck Γ Δ C₁ ⟨xs, φ, ys, ψ⟩ →
      DomCheck Δ C₁ ϑ →
      FDCheck Γ Δ (Program.pref C₁ C₂) ⟨xs, (fun ν => ϑ ν ∧ φ ν), ys, ψ⟩
  | prefRight {C₁ C₂ xs ys φ ψ ϑ} :
      FDCheck Γ Δ C₂ ⟨xs, φ, ys, ψ⟩ →
      DomCheck Δ C₁ ϑ →
      FDCheck Γ Δ (Program.pref C₁ C₂) ⟨xs, (fun ν => ¬ ϑ ν ∧ φ ν), ys, ψ⟩
  | weaken {C xs ws ys φ φ' ψ ψ'} :
      (∀ x, x ∈ ws → x ∈ xs) →
      (∀ ν, φ ν → φ' ν) →
      FDCheck Γ Δ C ⟨ws, φ', ys, ψ'⟩ →
      (∀ ν, ψ' ν → ψ ν) →
      FDCheck Γ Δ C ⟨xs, φ, ys, ψ⟩

theorem domain_overapprox {σ : TableVar → RelSem} {Δ : TableVar → Formula}
    (hΔ : EnvModelsDom σ Δ) :
    ∀ {C φ ν}, DomCheck Δ C φ → Defined (denote σ C) ν → φ ν := by
  intro C φ ν hdom
  induction hdom generalizing ν with
  | var =>
      intro hdef
      exact hΔ _ _ hdef
  | lit h =>
      intro hdef
      exact h _ hdef
  | filter h ih =>
      intro hdef
      rcases hdef with ⟨out, hout⟩
      exact ⟨ih ⟨out, hout.2⟩, hout.1⟩
  | seq h ih =>
      intro hdef
      rcases hdef with ⟨out, mid, h₁, h₂⟩
      exact ih ⟨mid, h₁⟩
  | join h₁ h₂ ih₁ ih₂ =>
      intro hdef
      rcases hdef with ⟨out, a₁, a₂, ν₁, ν₂, hc₁, hc₂, _⟩
      exact ⟨ih₁ ⟨(a₁, ν₁), hc₁⟩, ih₂ ⟨(a₂, ν₂), hc₂⟩⟩
  | pref h₁ h₂ ih₁ ih₂ =>
      intro hdef
      rcases hdef with ⟨out, hout⟩
      cases hout with
      | inl hleft =>
          exact Or.inl <| ih₁ ⟨out, hleft⟩
      | inr hright =>
          exact Or.inr <| ih₂ ⟨out, hright.2⟩

theorem type_soundness {σ : TableVar → RelSem} {Γ : TableVar → List GFD}
    {Δ : TableVar → Formula}
    (hΓ : EnvModelsFD σ Γ) (hΔ : EnvModelsDom σ Δ) :
    ∀ {C Φ}, FDCheck Γ Δ C Φ → Satisfies (denote σ C) Φ := by
  intro C Φ hfd
  induction hfd with
  | ctx hmem =>
      exact hΓ _ _ hmem
  | lit hs =>
      exact hs
  | refine h ih =>
      intro ν₁ ν₂ hg₁ hg₂ hag
      rcases ih hg₁.1 hg₂.1 hag with ⟨hdef₁, hdef₂, hpost₁, hpost₂, huniq⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rcases hdef₁ with ⟨out, hout⟩
        exact ⟨out, ⟨hg₁.2, hout⟩⟩
      · rcases hdef₂ with ⟨out, hout⟩
        exact ⟨out, ⟨hg₂.2, hout⟩⟩
      · intro out hout
        exact hpost₁ _ hout.2
      · intro out hout
        exact hpost₂ _ hout.2
      · intro out₁ out₂ hout₁ hout₂
        exact huniq _ _ hout₁.2 hout₂.2
  | compose h₁ h₂ ih₁ ih₂ =>
      rename_i C1 C2 xs ys zs φ θ ψ
      intro ν₁ ν₂ hg₁ hg₂ hag
      rcases ih₁ hg₁ hg₂ hag with ⟨hdef₁, hdef₂, hpost₁, hpost₂, huniq₁⟩
      rcases hdef₁ with ⟨mid₁, hm₁⟩
      rcases hdef₂ with ⟨mid₂, hm₂⟩
      have hmid : mid₁ = mid₂ := huniq₁ _ _ hm₁ hm₂
      subst mid₂
      have hmid_guard : _ := (hpost₁ _ hm₁).2
      have hagmid : agreesOn ys mid₁.2 mid₁.2 := by
        intro x hx
        rfl
      rcases ih₂ hmid_guard hmid_guard hagmid with
        ⟨hdefMid₁, hdefMid₂, hpostMid₁, hpostMid₂, huniq₂⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rcases hdefMid₁ with ⟨out, hout⟩
        exact ⟨out, ⟨mid₁, hm₁, hout⟩⟩
      · rcases hdefMid₂ with ⟨out, hout⟩
        exact ⟨out, ⟨mid₁, hm₂, hout⟩⟩
      · intro out hout
        rcases hout with ⟨mid, hmid, hout⟩
        have hguardMid : _ := (hpost₁ _ hmid).2
        have hagmid : agreesOn ys mid.2 mid.2 := by
          intro x hx
          rfl
        rcases ih₂ hguardMid hguardMid hagmid with
          ⟨_, _, hpostMid, _, _⟩
        exact hpostMid _ hout
      · intro out hout
        rcases hout with ⟨mid, hmid, hout⟩
        have hguardMid : _ := (hpost₂ _ hmid).2
        have hagmid : agreesOn ys mid.2 mid.2 := by
          intro x hx
          rfl
        rcases ih₂ hguardMid hguardMid hagmid with
          ⟨_, _, _, hpostMid, _⟩
        exact hpostMid _ hout
      · intro out₁ out₂ hout₁ hout₂
        rcases hout₁ with ⟨mid₁, hmid₁, hout₁⟩
        rcases hout₂ with ⟨mid₂, hmid₂, hout₂⟩
        have hmid : mid₁ = mid₂ := huniq₁ _ _ hmid₁ hmid₂
        subst mid₂
        have hguardMid : _ := (hpost₁ _ hmid₁).2
        have hagmid : agreesOn ys mid₁.2 mid₁.2 := by
          intro x hx
          rfl
        rcases ih₂ hguardMid hguardMid hagmid with
          ⟨_, _, _, _, huniq₂⟩
        exact huniq₂ _ _ hout₁ hout₂
  | join h₁ h₂ ih₁ ih₂ =>
      intro ν₁ ν₂ hg₁ hg₂ hag
      have hag₁ : agreesOn _ ν₁ ν₂ := agreesOn_of_mem_append_left hag
      have hag₂ : agreesOn _ ν₁ ν₂ := agreesOn_of_mem_append_right hag
      rcases ih₁ hg₁.1 hg₂.1 hag₁ with ⟨hdef₁₁, hdef₁₂, hpost₁₁, hpost₁₂, huniq₁⟩
      rcases ih₂ hg₁.2 hg₂.2 hag₂ with ⟨hdef₂₁, hdef₂₂, hpost₂₁, hpost₂₂, huniq₂⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rcases hdef₁₁ with ⟨out₁, hout₁⟩
        rcases hdef₂₁ with ⟨out₂, hout₂⟩
        exact ⟨(Action.pair out₁.1 out₂.1, mergeVal out₁.2 out₂.2),
          ⟨out₁.1, out₂.1, out₁.2, out₂.2, hout₁, hout₂, rfl⟩⟩
      · rcases hdef₁₂ with ⟨out₁, hout₁⟩
        rcases hdef₂₂ with ⟨out₂, hout₂⟩
        exact ⟨(Action.pair out₁.1 out₂.1, mergeVal out₁.2 out₂.2),
          ⟨out₁.1, out₂.1, out₁.2, out₂.2, hout₁, hout₂, rfl⟩⟩
      · intro out hout
        rcases hout with ⟨a₁, a₂, ν₁', ν₂', h₁', h₂', rfl⟩
        refine ⟨supportWithin_merge (hpost₁₁ _ h₁').1 (hpost₂₁ _ h₂').1, ?_⟩
        exact ⟨ν₁', ν₂', rfl, (hpost₁₁ _ h₁').2, (hpost₂₁ _ h₂').2,
          (hpost₁₁ _ h₁').1, (hpost₂₁ _ h₂').1⟩
      · intro out hout
        rcases hout with ⟨a₁, a₂, ν₁', ν₂', h₁', h₂', rfl⟩
        refine ⟨supportWithin_merge (hpost₁₂ _ h₁').1 (hpost₂₂ _ h₂').1, ?_⟩
        exact ⟨ν₁', ν₂', rfl, (hpost₁₂ _ h₁').2, (hpost₂₂ _ h₂').2,
          (hpost₁₂ _ h₁').1, (hpost₂₂ _ h₂').1⟩
      · intro out₁ out₂ hout₁ hout₂
        rcases hout₁ with ⟨a₁, a₂, ν₁a, ν₂a, h₁a, h₂a, rfl⟩
        rcases hout₂ with ⟨b₁, b₂, ν₁b, ν₂b, h₁b, h₂b, rfl⟩
        have hleft : (a₁, ν₁a) = (b₁, ν₁b) := huniq₁ _ _ h₁a h₁b
        have hright : (a₂, ν₂a) = (b₂, ν₂b) := huniq₂ _ _ h₂a h₂b
        cases hleft
        cases hright
        rfl
  | prefLeft hC hdom ih =>
      intro ν₁ ν₂ hg₁ hg₂ hag
      rcases ih hg₁.2 hg₂.2 hag with ⟨hdef₁, hdef₂, hpost₁, hpost₂, huniq⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rcases hdef₁ with ⟨out, hout⟩
        exact ⟨out, Or.inl hout⟩
      · rcases hdef₂ with ⟨out, hout⟩
        exact ⟨out, Or.inl hout⟩
      · intro out hout
        cases hout with
        | inl hleft =>
            exact hpost₁ _ hleft
        | inr hright =>
            exact False.elim <| hright.1 hdef₁
      · intro out hout
        cases hout with
        | inl hleft =>
            exact hpost₂ _ hleft
        | inr hright =>
            exact False.elim <| hright.1 hdef₂
      · intro out₁ out₂ hout₁ hout₂
        cases hout₁ with
        | inl hleft₁ =>
            cases hout₂ with
            | inl hleft₂ =>
                exact huniq _ _ hleft₁ hleft₂
            | inr hright₂ =>
                exact False.elim <| hright₂.1 hdef₂
        | inr hright₁ =>
            exact False.elim <| hright₁.1 hdef₁
  | prefRight hC hdom ih =>
      rename_i C1 C2 xs ys φ ψ θ
      intro ν₁ ν₂ hg₁ hg₂ hag
      rcases ih hg₁.2 hg₂.2 hag with ⟨hdef₁, hdef₂, hpost₁, hpost₂, huniq⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rcases hdef₁ with ⟨out, hout⟩
        exact ⟨out, Or.inr ⟨by
          intro hdef
          exact hg₁.1 <| domain_overapprox hΔ hdom hdef, hout⟩⟩
      · rcases hdef₂ with ⟨out, hout⟩
        exact ⟨out, Or.inr ⟨by
          intro hdef
          exact hg₂.1 <| domain_overapprox hΔ hdom hdef, hout⟩⟩
      · intro out hout
        cases hout with
        | inl hleft =>
            exact False.elim <| hg₁.1 <| domain_overapprox hΔ hdom ⟨out, hleft⟩
        | inr hright =>
            exact hpost₁ _ hright.2
      · intro out hout
        cases hout with
        | inl hleft =>
            exact False.elim <| hg₂.1 <| domain_overapprox hΔ hdom ⟨out, hleft⟩
        | inr hright =>
            exact hpost₂ _ hright.2
      · intro out₁ out₂ hout₁ hout₂
        cases hout₁ with
        | inl hleft₁ =>
            exact False.elim <| hg₁.1 <| domain_overapprox hΔ hdom ⟨out₁, hleft₁⟩
        | inr hright₁ =>
            cases hout₂ with
            | inl hleft₂ =>
                exact False.elim <| hg₂.1 <| domain_overapprox hΔ hdom ⟨out₂, hleft₂⟩
            | inr hright₂ =>
                exact huniq _ _ hright₁.2 hright₂.2
  | weaken hsub hguard hC hpost ih =>
      intro ν₁ ν₂ hg₁ hg₂ hag
      rcases ih (hguard _ hg₁) (hguard _ hg₂) (by
        intro x hx
        exact hag x (hsub x hx)) with ⟨hdef₁, hdef₂, hpost₁, hpost₂, huniq⟩
      refine ⟨hdef₁, hdef₂, ?_, ?_, ?_⟩
      · intro out hout
        exact ⟨(hpost₁ _ hout).1, hpost _ (hpost₁ _ hout).2⟩
      · intro out hout
        exact ⟨(hpost₂ _ hout).1, hpost _ (hpost₂ _ hout).2⟩
      · exact huniq

end Proofs
