import Proofs.Basic

open Classical

namespace Proofs

noncomputable section

structure Row where
  guard : Formula
  act : Action
  out : Valuation

structure Table where
  rows : List Row

def Row.eval (ρ : Row) (ν : Valuation) : Option (Action × Valuation) :=
  if ρ.guard ν then some (ρ.act, ρ.out) else none

def evalRows : List Row → Valuation → Option (Action × Valuation)
  | [], _ => none
  | ρ :: rs, ν =>
      match ρ.eval ν with
      | some out => some out
      | none => evalRows rs ν

def Table.eval (T : Table) (ν : Valuation) : Option (Action × Valuation) :=
  evalRows T.rows ν

def Table.run (T : Table) : RelSem :=
  fun ν out => T.eval ν = some out

def Table.empty : Table := ⟨[]⟩

def Table.unit (ρ : Row) : Table := ⟨[ρ]⟩

def Table.after (T₁ T₂ : Table) : Table :=
  ⟨T₁.rows ++ T₂.rows⟩

def Table.map (f : Row → Row) (T : Table) : Table :=
  ⟨T.rows.map f⟩

def bindRows : List Row → (Row → Table) → List Row
  | [], _ => []
  | ρ :: rs, f => (f ρ).rows ++ bindRows rs f

def bindRows? : List Row → (Row → Option Table) → Option (List Row)
  | [], _ => some []
  | ρ :: rs, f =>
      match f ρ, bindRows? rs f with
      | some T, some rows => some (T.rows ++ rows)
      | _, _ => none

def Table.bind (T : Table) (f : Row → Table) : Table :=
  ⟨bindRows T.rows f⟩

def Table.bind? (T : Table) (f : Row → Option Table) : Option Table := do
  let rows ← bindRows? T.rows f
  pure ⟨rows⟩

def semEnv (σ : TableVar → Table) : TableVar → RelSem :=
  fun t => (σ t).run

inductive IProgram where
  | lit : Table → IProgram
  | var : TableVar → IProgram
  | filter : Formula → IProgram → IProgram
  | seq : IProgram → IProgram → IProgram
  | join : IProgram → IProgram → IProgram
  | pref : IProgram → IProgram → IProgram

def erase : IProgram → Program
  | .lit T => Program.lit T.run
  | .var t => Program.var t
  | .filter φ C => Program.filter φ (erase C)
  | .seq C₁ C₂ => Program.seq (erase C₁) (erase C₂)
  | .join C₁ C₂ => Program.join (erase C₁) (erase C₂)
  | .pref C₁ C₂ => Program.pref (erase C₁) (erase C₂)

def denoteOpt (σ : TableVar → Table) : IProgram → Valuation → Option (Action × Valuation)
  | .lit T, ν => T.eval ν
  | .var t, ν => (σ t).eval ν
  | .filter φ C, ν =>
      if φ ν then denoteOpt σ C ν else none
  | .seq C₁ C₂, ν =>
      match denoteOpt σ C₁ ν with
      | some mid => denoteOpt σ C₂ mid.2
      | none => none
  | .join C₁ C₂, ν =>
      match denoteOpt σ C₁ ν, denoteOpt σ C₂ ν with
      | some out₁, some out₂ => some (Action.pair out₁.1 out₂.1, mergeVal out₁.2 out₂.2)
      | _, _ => none
  | .pref C₁ C₂, ν =>
      match denoteOpt σ C₁ ν with
      | some out => some out
      | none => denoteOpt σ C₂ ν

def splitRow (φ : Formula) (ρ : Row) : Row :=
  { ρ with guard := fun ν => ρ.guard ν ∧ φ ν }

def seqRow (T₂ : Table) (ρ : Row) : Option Table :=
  match T₂.eval ρ.out with
  | some out => some <| Table.unit { guard := ρ.guard, act := out.1, out := out.2 }
  | none => none

def joinRow (ρ₁ ρ₂ : Row) : Row :=
  { guard := fun ν => ρ₁.guard ν ∧ ρ₂.guard ν
    act := Action.pair ρ₁.act ρ₂.act
    out := mergeVal ρ₁.out ρ₂.out }

def joinRows : List Row → List Row → List Row
  | [], _ => []
  | ρ :: rs, rs₂ => List.map (joinRow ρ) rs₂ ++ joinRows rs rs₂

def seqRows : List Row → Table → Option (List Row)
  | [], _ => some []
  | ρ :: rs, T₂ =>
      match T₂.eval ρ.out, seqRows rs T₂ with
      | some out, some rows =>
          some ({ guard := ρ.guard, act := out.1, out := out.2 } :: rows)
      | _, _ => none

def compileSeqTable (T₁ T₂ : Table) : Option Table := do
  let rows ← seqRows T₁.rows T₂
  pure ⟨rows⟩

def compile (σ : TableVar → Table) : IProgram → Option Table
  | .lit T => some T
  | .var t => some (σ t)
  | .filter φ C => do
      let T ← compile σ C
      pure <| T.map (splitRow φ)
  | .seq C₁ C₂ => do
      let T₁ ← compile σ C₁
      let T₂ ← compile σ C₂
      compileSeqTable T₁ T₂
  | .join C₁ C₂ => do
      let T₁ ← compile σ C₁
      let T₂ ← compile σ C₂
      pure ⟨joinRows T₁.rows T₂.rows⟩
  | .pref C₁ C₂ => do
      let T₁ ← compile σ C₁
      let T₂ ← compile σ C₂
      pure <| T₁.after T₂

def EnvModelsDomT (σ : TableVar → Table) (Δ : TableVar → Formula) : Prop :=
  EnvModelsDom (semEnv σ) Δ

def EnvModelsFDT (σ : TableVar → Table) (Γ : TableVar → List GFD) : Prop :=
  EnvModelsFD (semEnv σ) Γ

theorem run_iff_eval {T : Table} {ν : Valuation} {out : Action × Valuation} :
    T.run ν out ↔ T.eval ν = some out := by
  rfl

theorem defined_run_iff {T : Table} {ν : Valuation} :
    Defined T.run ν ↔ T.eval ν ≠ none := by
  constructor
  · intro h
    rcases h with ⟨out, hout⟩
    simp [Table.run] at hout
    simp [hout]
  · intro h
    cases hEval : T.eval ν with
    | none =>
        contradiction
    | some out =>
        exact ⟨out, hEval⟩

theorem evalRows_append (rs₁ rs₂ : List Row) (ν : Valuation) :
    evalRows (rs₁ ++ rs₂) ν =
      match evalRows rs₁ ν with
      | some out => some out
      | none => evalRows rs₂ ν := by
  induction rs₁ with
  | nil =>
      simp [evalRows]
  | cons ρ rs ih =>
      simp [evalRows, ih]
      split <;> rfl

theorem after_eval (T₁ T₂ : Table) (ν : Valuation) :
    (T₁.after T₂).eval ν =
      match T₁.eval ν with
      | some out => some out
      | none => T₂.eval ν := by
  simpa [Table.after, Table.eval] using evalRows_append T₁.rows T₂.rows ν

theorem unit_eval (ρ : Row) (ν : Valuation) :
    (Table.unit ρ).eval ν = ρ.eval ν := by
  by_cases h : ρ.guard ν <;> simp [Table.unit, Table.eval, evalRows, Row.eval, h]

theorem map_split_evalRows (φ : Formula) (rs : List Row) (ν : Valuation) :
    evalRows (rs.map (splitRow φ)) ν =
      if φ ν then evalRows rs ν else none := by
  induction rs with
  | nil =>
      simp [evalRows]
  | cons ρ rs ih =>
      simp [splitRow, evalRows, Row.eval, ih]
      by_cases hρ : ρ.guard ν <;> by_cases hφ : φ ν <;> simp [hρ, hφ]

theorem map_split_eval (φ : Formula) (T : Table) (ν : Valuation) :
    (T.map (splitRow φ)).eval ν =
      if φ ν then T.eval ν else none := by
  simpa [Table.map, Table.eval] using map_split_evalRows φ T.rows ν

theorem joinBlock_eval (ρ : Row) (rs : List Row) (ν : Valuation) :
    evalRows (List.map (joinRow ρ) rs) ν =
      if ρ.guard ν then
        Option.map (fun out => (Action.pair ρ.act out.1, mergeVal ρ.out out.2)) (evalRows rs ν)
      else none := by
  induction rs with
  | nil =>
      simp [evalRows]
  | cons ρ₂ rs ih =>
      simp [evalRows, Row.eval, joinRow, ih]
      by_cases hρ : ρ.guard ν <;> by_cases hρ₂ : ρ₂.guard ν <;> simp [hρ, hρ₂]

theorem joinRows_eval (rs₁ rs₂ : List Row) (ν : Valuation) :
    evalRows (joinRows rs₁ rs₂) ν =
      match evalRows rs₁ ν, evalRows rs₂ ν with
      | some out₁, some out₂ => some (Action.pair out₁.1 out₂.1, mergeVal out₁.2 out₂.2)
      | _, _ => none := by
  induction rs₁ with
  | nil =>
      simp [joinRows, evalRows]
  | cons ρ rs ih =>
      simp [joinRows, evalRows_append, joinBlock_eval, ih]
      by_cases hρ : ρ.guard ν
      · cases hR : evalRows rs₂ ν <;> simp [evalRows, Row.eval, hρ]
      · simp [evalRows, Row.eval, hρ]

theorem seqRows_eval {rs : List Row} {T₂ : Table} {rows' : List Row}
    (hseq : seqRows rs T₂ = some rows') (ν : Valuation) :
    evalRows rows' ν =
      match evalRows rs ν with
      | some mid => T₂.eval mid.2
      | none => none := by
  induction rs generalizing rows' with
  | nil =>
      simp [seqRows] at hseq
      simp [hseq, evalRows]
  | cons ρ rs ih =>
      cases hT₂ : T₂.eval ρ.out with
      | none =>
          simp [seqRows, hT₂] at hseq
      | some out =>
          cases hRest : seqRows rs T₂ with
          | none =>
              simp [seqRows, hT₂, hRest] at hseq
          | some rest =>
              simp [seqRows, hT₂, hRest] at hseq
              cases hseq
              simp [evalRows, Row.eval]
              by_cases hρ : ρ.guard ν
              · simp [hρ, hT₂]
              · simp [hρ, ih hRest]

theorem table_run_some_iff {T : Table} {ν : Valuation} {out : Action × Valuation} :
    T.run ν out ↔ T.eval ν = some out := by
  rfl

theorem denoteOpt_some_iff (σ : TableVar → Table) :
    ∀ (C : IProgram) (ν : Valuation) (out : Action × Valuation),
      denoteOpt σ C ν = some out ↔ denote (semEnv σ) (erase C) ν out := by
  intro C
  induction C with
  | lit T =>
      intro ν out
      rfl
  | var t =>
      intro ν out
      rfl
  | filter φ C ih =>
      intro ν out
      by_cases hφ : φ ν
      · simp [denoteOpt, erase, hφ, ih, denote]
      · simp [denoteOpt, erase, hφ, denote]
  | seq C₁ C₂ ih₁ ih₂ =>
      intro ν out
      constructor
      · intro h
        simp [denoteOpt] at h
        rcases h₁ : denoteOpt σ C₁ ν with _ | mid <;> simp [h₁] at h
        exact ⟨mid, (ih₁ _ _).1 h₁, (ih₂ _ _).1 h⟩
      · intro h
        rcases h with ⟨mid, h₁, h₂⟩
        have hmid : denoteOpt σ C₁ ν = some mid := (ih₁ _ _).2 h₁
        have hout : denoteOpt σ C₂ mid.2 = some out := (ih₂ _ _).2 h₂
        simp [denoteOpt, hmid, hout]
  | join C₁ C₂ ih₁ ih₂ =>
      intro ν out
      constructor
      · intro h
        simp [denoteOpt] at h
        rcases h₁ : denoteOpt σ C₁ ν with _ | out₁ <;> simp [h₁] at h
        rcases h₂ : denoteOpt σ C₂ ν with _ | out₂ <;> simp [h₂] at h
        rcases h with rfl
        exact ⟨out₁.1, out₂.1, out₁.2, out₂.2, (ih₁ _ _).1 h₁, (ih₂ _ _).1 h₂, rfl⟩
      · intro h
        rcases h with ⟨a₁, a₂, ν₁, ν₂, h₁, h₂, rfl⟩
        have h₁' : denoteOpt σ C₁ ν = some (a₁, ν₁) := (ih₁ _ _).2 h₁
        have h₂' : denoteOpt σ C₂ ν = some (a₂, ν₂) := (ih₂ _ _).2 h₂
        simp [denoteOpt, h₁', h₂']
  | pref C₁ C₂ ih₁ ih₂ =>
      intro ν out
      constructor
      · intro h
        simp [denoteOpt] at h
        rcases h₁ : denoteOpt σ C₁ ν with _ | out₁
        · simp [h₁] at h
          exact Or.inr ⟨by
            intro hdef
            rcases hdef with ⟨out', hout'⟩
            have : denoteOpt σ C₁ ν = some out' := (ih₁ _ _).2 hout'
            simp [h₁] at this, (ih₂ _ _).1 h⟩
        · simp [h₁] at h
          cases h
          exact Or.inl ((ih₁ _ _).1 h₁)
      · intro h
        cases h with
        | inl hleft =>
            have h₁ : denoteOpt σ C₁ ν = some out := (ih₁ _ _).2 hleft
            simp [denoteOpt, h₁]
        | inr hright =>
            rcases hright with ⟨hundef, hright⟩
            have h₂ : denoteOpt σ C₂ ν = some out := (ih₂ _ _).2 hright
            have hnone : denoteOpt σ C₁ ν = none := by
              cases h₁ : denoteOpt σ C₁ ν with
              | none => rfl
              | some out₁ =>
                  exfalso
                  apply hundef
                  exact ⟨out₁, (ih₁ _ _).1 h₁⟩
            simp [denoteOpt, hnone, h₂]

theorem denoteOpt_none_iff (σ : TableVar → Table) :
    ∀ (C : IProgram) (ν : Valuation),
      denoteOpt σ C ν = none ↔ ¬ Defined (denote (semEnv σ) (erase C)) ν := by
  intro C ν
  constructor
  · intro hnone hdef
    rcases hdef with ⟨out, hout⟩
    have : denoteOpt σ C ν = some out := (denoteOpt_some_iff σ C ν out).2 hout
    simp [hnone] at this
  · intro hundef
    cases h : denoteOpt σ C ν with
    | none =>
        rfl
    | some out =>
        exfalso
        apply hundef
        exact ⟨out, (denoteOpt_some_iff σ C ν out).1 h⟩

theorem compile_eval (σ : TableVar → Table) :
    ∀ {C T ν}, compile σ C = some T → T.eval ν = denoteOpt σ C ν := by
  intro C
  induction C with
  | lit T =>
      intro T' ν hcomp
      simp [compile] at hcomp
      cases hcomp
      rfl
  | var t =>
      intro T' ν hcomp
      simp [compile] at hcomp
      cases hcomp
      rfl
  | filter φ C ih =>
      intro T ν hcomp
      cases hC : compile σ C with
      | none =>
          simp [compile, hC] at hcomp
      | some TC =>
          simp [compile, hC] at hcomp
          cases hcomp
          rw [map_split_eval, ih hC]
          by_cases hφ : φ ν <;> simp [denoteOpt, hφ]
  | seq C₁ C₂ ih₁ ih₂ =>
      intro T ν hcomp
      cases h₁ : compile σ C₁ with
      | none =>
          simp [compile, h₁] at hcomp
      | some T₁ =>
          cases h₂ : compile σ C₂ with
          | none =>
              simp [compile, h₁, h₂] at hcomp
          | some T₂ =>
              cases hseq : compileSeqTable T₁ T₂ with
              | none =>
                  simp [compile, h₁, h₂, hseq] at hcomp
              | some TC =>
                  simp [compile, h₁, h₂, hseq] at hcomp
                  cases hcomp
                  have hrows : seqRows T₁.rows T₂ = some T.rows := by
                    unfold compileSeqTable at hseq
                    cases hs : seqRows T₁.rows T₂ with
                    | none =>
                        simp [hs] at hseq
                    | some rows =>
                        simp [hs] at hseq
                        cases hseq
                        simp
                  rw [Table.eval]
                  rw [seqRows_eval hrows ν]
                  change
                    (match T₁.eval ν with
                      | some mid => T₂.eval mid.2
                      | none => none) =
                    denoteOpt σ (C₁.seq C₂) ν
                  rw [ih₁ h₁]
                  cases hmid : denoteOpt σ C₁ ν with
                  | none =>
                      simp [denoteOpt, hmid]
                  | some mid =>
                      simp [denoteOpt, hmid]
                      rw [ih₂ (T := T₂) (ν := mid.2) h₂]
  | join C₁ C₂ ih₁ ih₂ =>
      intro T ν hcomp
      cases h₁ : compile σ C₁ with
      | none =>
          simp [compile, h₁] at hcomp
      | some T₁ =>
          cases h₂ : compile σ C₂ with
          | none =>
              simp [compile, h₁, h₂] at hcomp
          | some T₂ =>
              simp [compile, h₁, h₂] at hcomp
              cases hcomp
              rw [Table.eval, joinRows_eval]
              have hE₁ : T₁.eval ν = denoteOpt σ C₁ ν := ih₁ h₁
              have hE₂ : T₂.eval ν = denoteOpt σ C₂ ν := ih₂ h₂
              change
                (match T₁.eval ν, T₂.eval ν with
                  | some out₁, some out₂ => some (Action.pair out₁.1 out₂.1, mergeVal out₁.2 out₂.2)
                  | _, _ => none) =
                (match denoteOpt σ C₁ ν, denoteOpt σ C₂ ν with
                  | some out₁, some out₂ => some (Action.pair out₁.1 out₂.1, mergeVal out₁.2 out₂.2)
                  | _, _ => none)
              rw [hE₁, hE₂]
  | pref C₁ C₂ ih₁ ih₂ =>
      intro T ν hcomp
      cases h₁ : compile σ C₁ with
      | none =>
          simp [compile, h₁] at hcomp
      | some T₁ =>
          cases h₂ : compile σ C₂ with
          | none =>
              simp [compile, h₁, h₂] at hcomp
          | some T₂ =>
              simp [compile, h₁, h₂] at hcomp
              cases hcomp
              rw [after_eval, ih₁ h₁, ih₂ h₂]
              cases h : denoteOpt σ C₁ ν <;> simp [denoteOpt, h]

theorem compiler_refinement {σ : TableVar → Table} {C : IProgram} {T : Table}
    (hcomp : compile σ C = some T) :
    ∀ {ν : Valuation} {out : Action × Valuation}, T.run ν out → denote (semEnv σ) (erase C) ν out := by
  intro ν out hrun
  have heval : T.eval ν = some out := hrun
  rw [compile_eval σ hcomp] at heval
  exact (denoteOpt_some_iff σ C ν out).1 heval

theorem compiler_complete {σ : TableVar → Table} {C : IProgram} {T : Table}
    (hcomp : compile σ C = some T) :
    ∀ {ν : Valuation} {out : Action × Valuation}, denote (semEnv σ) (erase C) ν out → T.run ν out := by
  intro ν out hden
  have heval : denoteOpt σ C ν = some out := (denoteOpt_some_iff σ C ν out).2 hden
  show T.eval ν = some out
  rw [compile_eval σ hcomp]
  exact heval

theorem compiler_domain_preservation {σ : TableVar → Table} {Δ : TableVar → Formula}
    (hΔ : EnvModelsDomT σ Δ) {C : IProgram} {φ : Formula} {ν : Valuation}
    (hdom : DomCheck Δ (erase C) φ) {T : Table}
    (hcomp : compile σ C = some T) :
    Defined T.run ν → φ ν := by
  intro hdef
  exact domain_overapprox hΔ hdom <| by
    rcases hdef with ⟨out, hout⟩
    exact ⟨out, compiler_refinement hcomp hout⟩

theorem compiler_type_preservation {σ : TableVar → Table} {Γ : TableVar → List GFD}
    {Δ : TableVar → Formula}
    (hΓ : EnvModelsFDT σ Γ) (hΔ : EnvModelsDomT σ Δ)
    {C : IProgram} {Φ : GFD} (hfd : FDCheck Γ Δ (erase C) Φ) {T : Table}
    (hcomp : compile σ C = some T) :
    Satisfies T.run Φ := by
  intro ν₁ ν₂ hg₁ hg₂ hag
  rcases type_soundness hΓ hΔ hfd hg₁ hg₂ hag with ⟨hdef₁, hdef₂, hpost₁, hpost₂, huniq⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hdef₁ with ⟨out, hout⟩
    exact ⟨out, compiler_complete hcomp hout⟩
  · rcases hdef₂ with ⟨out, hout⟩
    exact ⟨out, compiler_complete hcomp hout⟩
  · intro out hout
    exact hpost₁ _ (compiler_refinement hcomp hout)
  · intro out hout
    exact hpost₂ _ (compiler_refinement hcomp hout)
  · intro out₁ out₂ hout₁ hout₂
    exact huniq _ _ (compiler_refinement hcomp hout₁) (compiler_refinement hcomp hout₂)

def EquivalentModulo (σ : TableVar → Table) (C : IProgram) (T : Table) (Φ : GFD) : Prop :=
  ∀ ⦃ν₁ ν₂ : Valuation⦄ ⦃out₁ out₂ : Action × Valuation⦄,
    Φ.guard ν₁ →
    Φ.guard ν₂ →
    agreesOn Φ.xs ν₁ ν₂ →
    denote (semEnv σ) (erase C) ν₁ out₁ →
    T.run ν₂ out₂ →
    out₁ = out₂

theorem compiler_correctness {σ : TableVar → Table} {Γ : TableVar → List GFD}
    {Δ : TableVar → Formula}
    (hΓ : EnvModelsFDT σ Γ) (hΔ : EnvModelsDomT σ Δ)
    {C : IProgram} {Φ : GFD} (hfd : FDCheck Γ Δ (erase C) Φ) {T : Table}
    (hcomp : compile σ C = some T) :
    EquivalentModulo σ C T Φ := by
  intro ν₁ ν₂ out₁ out₂ hg₁ hg₂ hag h₁ h₂
  rcases compiler_type_preservation hΓ hΔ hfd hcomp hg₁ hg₂ hag with ⟨_, _, _, _, huniq⟩
  exact huniq _ _ (compiler_complete hcomp h₁) h₂

end

end Proofs
