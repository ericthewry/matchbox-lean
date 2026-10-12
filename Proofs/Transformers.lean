import Proofs.Basic

open Classical

namespace Proofs

def Valuation.write (ν : Valuation) (x : Var) (v : Value) : Valuation :=
  fun y => if y = x then some v else ν y

def Valuation.proj (ν : Valuation) (xs : List Var) : Valuation :=
  fun y => if y ∈ xs then ν y else none

theorem supportWithin_write {xs : List Var} {ν : Valuation} {x : Var} {v : Value}
    (h : supportWithin xs ν) :
    supportWithin (x :: xs) (ν.write x v) := by
  intro y hy
  by_cases hxy : y = x
  · exact List.mem_cons.mpr <| Or.inl hxy
  · have hy' : ν y ≠ none := by
      simpa [Valuation.write, hxy] using hy
    exact List.mem_cons.mpr <| Or.inr (h y hy')

theorem supportWithin_proj {xs : List Var} {ν : Valuation} :
    supportWithin xs (ν.proj xs) := by
  intro y hy
  by_cases h : y ∈ xs
  · simp [h]
  · simp [Valuation.proj, h] at hy

theorem eq_of_supportWithin_agreesOn {xs : List Var} {ν₁ ν₂ : Valuation}
    (h₁ : supportWithin xs ν₁) (h₂ : supportWithin xs ν₂) (hag : agreesOn xs ν₁ ν₂) :
    ν₁ = ν₂ := by
  funext x
  by_cases hx₁ : ν₁ x = none
  · by_cases hx₂ : ν₂ x = none
    · simp [hx₁, hx₂]
    · have hxmem : x ∈ xs := h₂ x hx₂
      have hEq := hag x hxmem
      rw [hx₁] at hEq
      exact hx₁.trans hEq
  · have hxmem : x ∈ xs := h₁ x hx₁
    exact hag x hxmem

structure Expr where
  deps : List Var
  eval : Valuation → Value
  respects : ∀ {ν₁ ν₂ : Valuation}, agreesOn deps ν₁ ν₂ → eval ν₁ = eval ν₂

abbrev ValSem := Valuation → Valuation → Prop

def ValDefined (f : ValSem) (ν : Valuation) : Prop := ∃ ν', f ν ν'

def ValSatisfies (f : ValSem) (xs : List Var) (guard : Formula) (ys : List Var) (post : Formula) : Prop :=
  ∀ ⦃ν₁ ν₂ : Valuation⦄,
    guard ν₁ →
    guard ν₂ →
    agreesOn xs ν₁ ν₂ →
    ValDefined f ν₁ ∧
    ValDefined f ν₂ ∧
    (∀ out, f ν₁ out → supportWithin ys out ∧ post out) ∧
    (∀ out, f ν₂ out → supportWithin ys out ∧ post out) ∧
    ∀ out₁ out₂, f ν₁ out₁ → f ν₂ out₂ → out₁ = out₂

def writeSem (x : Var) (e : Expr) : ValSem :=
  fun ν ν' => ν' = ν.write x (e.eval ν)

def projSem (xs : List Var) : ValSem :=
  fun ν ν' => ν' = ν.proj xs

theorem write_tfx_sound {xs : List Var} {x : Var} {e : Expr} {ψ : Formula} :
    ValSatisfies (writeSem x e)
      xs
      (fun ν => supportWithin xs ν ∧ ψ (ν.write x (e.eval ν)))
      (x :: xs)
      ψ := by
  intro ν₁ ν₂ hg₁ hg₂ hag
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨ν₁.write x (e.eval ν₁), rfl⟩
  · exact ⟨ν₂.write x (e.eval ν₂), rfl⟩
  · intro out hout
    subst hout
    exact ⟨supportWithin_write hg₁.1, hg₁.2⟩
  · intro out hout
    subst hout
    exact ⟨supportWithin_write hg₂.1, hg₂.2⟩
  · intro out₁ out₂ hout₁ hout₂
    subst hout₁
    subst hout₂
    have hEq : ν₁ = ν₂ := eq_of_supportWithin_agreesOn hg₁.1 hg₂.1 hag
    subst hEq
    rfl

theorem proj_tfx_sound {xs : List Var} {guard : Formula}
    (huniq :
      ∀ ⦃ν₁ ν₂ : Valuation⦄,
        guard ν₁ → guard ν₂ → agreesOn xs ν₁ ν₂ → ν₁ = ν₂) :
    ValSatisfies (projSem xs)
      xs
      guard
      xs
      (fun ν' => ∃ ν, projSem xs ν ν' ∧ guard ν) := by
  intro ν₁ ν₂ hg₁ hg₂ hag
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨ν₁.proj xs, rfl⟩
  · exact ⟨ν₂.proj xs, rfl⟩
  · intro out hout
    subst hout
    exact ⟨supportWithin_proj, ⟨ν₁, rfl, hg₁⟩⟩
  · intro out hout
    subst hout
    exact ⟨supportWithin_proj, ⟨ν₂, rfl, hg₂⟩⟩
  · intro out₁ out₂ hout₁ hout₂
    subst hout₁
    subst hout₂
    have hEq : ν₁ = ν₂ := huniq hg₁ hg₂ hag
    subst hEq
    rfl

def renameRange (src dst : String) (f : RelSem) : RelSem :=
  fun ν out =>
    ∃ act ν', f ν (act, ν') ∧
      out = ((if act = Action.atom src then Action.atom dst else act), ν')

theorem rename_preserves_satisfies {σ : RelSem} {Φ : GFD} {src dst : String}
    (hσ : Satisfies σ Φ) :
    Satisfies (renameRange src dst σ) Φ := by
  intro ν₁ ν₂ hg₁ hg₂ hag
  rcases hσ hg₁ hg₂ hag with ⟨hdef₁, hdef₂, hpost₁, hpost₂, huniq⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hdef₁ with ⟨out, hout⟩
    exact ⟨((if out.1 = Action.atom src then Action.atom dst else out.1), out.2), ⟨out.1, out.2, hout, rfl⟩⟩
  · rcases hdef₂ with ⟨out, hout⟩
    exact ⟨((if out.1 = Action.atom src then Action.atom dst else out.1), out.2), ⟨out.1, out.2, hout, rfl⟩⟩
  · intro out hout
    rcases hout with ⟨act, ν', hσ', rfl⟩
    exact hpost₁ (act, ν') hσ'
  · intro out hout
    rcases hout with ⟨act, ν', hσ', rfl⟩
    exact hpost₂ (act, ν') hσ'
  · intro out₁ out₂ hout₁ hout₂
    rcases hout₁ with ⟨act₁, ν₁', hσ₁, hout₁⟩
    rcases hout₂ with ⟨act₂, ν₂', hσ₂, hout₂⟩
    have hEq : (act₁, ν₁') = (act₂, ν₂') := huniq _ _ hσ₁ hσ₂
    cases hEq
    simp [hout₁, hout₂]

end Proofs
