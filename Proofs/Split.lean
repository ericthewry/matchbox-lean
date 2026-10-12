import Proofs.Compiler

open Classical

namespace Proofs

noncomputable section

structure GuardLang where
  Guard : Type
  holds : Guard → Formula

structure SplitOracle (space : List Valuation) (H : GuardLang) where
  choose : (witness : Valuation) → (residual : List Valuation) → witness ∈ residual → H.Guard
  hits :
    ∀ {witness residual} (hmem : witness ∈ residual),
      H.holds (choose witness residual hmem) witness
  subset :
    ∀ {witness residual} (hmem : witness ∈ residual) {ν : Valuation},
      ν ∈ space →
      H.holds (choose witness residual hmem) ν →
      ν ∈ residual

def residualVals (space : List Valuation) (ρ : Row) (φ : Formula) : List Valuation :=
  space.filter (fun ν => decide (ρ.guard ν ∧ φ ν))

def emittedRow (space : List Valuation) (H : GuardLang) (ρ : Row) (g : H.Guard) : Row :=
  { guard := fun ν => ν ∈ space ∧ H.holds g ν
    act := ρ.act
    out := ρ.out }

def dropCovered (H : GuardLang) (g : H.Guard) (residual : List Valuation) : List Valuation :=
  residual.filter (fun ν => !(decide (H.holds g ν)))

def splitGuardsFuel {space : List Valuation} {H : GuardLang} (O : SplitOracle space H) :
    Nat → List Valuation → List H.Guard
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, witness :: rest =>
      let g := O.choose witness (witness :: rest) (by simp)
      g :: splitGuardsFuel O fuel (dropCovered H g rest)

def splitGuards {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (residual : List Valuation) : List H.Guard :=
  splitGuardsFuel O residual.length residual

def splitTable {space : List Valuation} {H : GuardLang} (O : SplitOracle space H) (ρ : Row)
    (φ : Formula) : Table :=
  ⟨(splitGuards O (residualVals space ρ φ)).map (emittedRow space H ρ)⟩

def GuardCovered (H : GuardLang) (gs : List H.Guard) (ν : Valuation) : Prop :=
  ∃ g ∈ gs, H.holds g ν

def RowsMatch (space : List Valuation) (H : GuardLang) (gs : List H.Guard) (ν : Valuation) : Prop :=
  ∃ g ∈ gs, ν ∈ space ∧ H.holds g ν

theorem mem_residualVals_iff {space : List Valuation} {ρ : Row} {φ : Formula} {ν : Valuation} :
    ν ∈ residualVals space ρ φ ↔ ν ∈ space ∧ ρ.guard ν ∧ φ ν := by
  simp [residualVals]

theorem residualVals_mem_space {space : List Valuation} {ρ : Row} {φ : Formula} {ν : Valuation}
    (hmem : ν ∈ residualVals space ρ φ) : ν ∈ space := by
  exact (mem_residualVals_iff.mp hmem).1

theorem splitGuardsFuel_complete {space : List Valuation} {H : GuardLang} (O : SplitOracle space H) :
    ∀ {fuel residual ν},
      residual.length ≤ fuel →
      (∀ μ, μ ∈ residual → μ ∈ space) →
      ν ∈ residual →
      GuardCovered H (splitGuardsFuel O fuel residual) ν := by
  intro fuel
  induction fuel with
  | zero =>
      intro residual ν hlen hspace hmem
      have hnil : residual = [] := by
        cases residual with
        | nil => rfl
        | cons witness rest =>
            simp at hlen
      subst hnil
      cases hmem
  | succ fuel ih =>
      intro residual ν hlen hspace hmem
      cases residual with
      | nil =>
          cases hmem
      | cons witness rest =>
          let g := O.choose witness (witness :: rest) (by simp)
          simp at hmem
          cases hmem with
          | inl hEq =>
              subst hEq
              refine ⟨g, ?_, O.hits (by simp)⟩
              simp [splitGuardsFuel, g]
          | inr hmemRest =>
              by_cases hg : H.holds g ν
              · refine ⟨g, ?_, hg⟩
                simp [splitGuardsFuel, g]
              · have hlenRest : rest.length ≤ fuel := by
                  simpa using hlen
                have hlen' : (dropCovered H g rest).length ≤ fuel := by
                  exact Nat.le_trans (List.length_filter_le _ rest) hlenRest
                have hmem' : ν ∈ dropCovered H g rest := by
                  simp [dropCovered, hmemRest, hg]
                have hspace' : ∀ μ, μ ∈ dropCovered H g rest → μ ∈ space := by
                  intro μ hμ
                  have hμrest : μ ∈ rest := by
                    simp [dropCovered] at hμ
                    exact hμ.1
                  exact hspace μ (by simp [hμrest])
                rcases ih hlen' hspace' hmem' with ⟨g', hg'mem, hg'ν⟩
                exact ⟨g', by simp [splitGuardsFuel, g, hg'mem], hg'ν⟩

theorem splitGuards_complete {space : List Valuation} {H : GuardLang} (O : SplitOracle space H) :
    ∀ {residual ν},
      (∀ μ, μ ∈ residual → μ ∈ space) →
      ν ∈ residual →
      GuardCovered H (splitGuards O residual) ν := by
  intro residual ν hspace hmem
  unfold splitGuards
  exact splitGuardsFuel_complete O (fuel := residual.length) (Nat.le_refl _) hspace hmem

theorem splitGuardsFuel_sound {space : List Valuation} {H : GuardLang} (O : SplitOracle space H) :
    ∀ {fuel residual ν},
      residual.length ≤ fuel →
      (∀ μ, μ ∈ residual → μ ∈ space) →
      ν ∈ space →
      GuardCovered H (splitGuardsFuel O fuel residual) ν →
      ν ∈ residual := by
  intro fuel
  induction fuel with
  | zero =>
      intro residual ν hlen hspace hνspace hcov
      have hnil : residual = [] := by
        cases residual with
        | nil => rfl
        | cons witness rest =>
            simp at hlen
      subst hnil
      rcases hcov with ⟨g, hgmem, _⟩
      simp [splitGuardsFuel] at hgmem
  | succ fuel ih =>
      intro residual ν hlen hspace hνspace hcov
      cases residual with
      | nil =>
          rcases hcov with ⟨g, hgmem, _⟩
          simp [splitGuardsFuel] at hgmem
      | cons witness rest =>
          let g := O.choose witness (witness :: rest) (by simp)
          simp [GuardCovered, splitGuardsFuel] at hcov
          rcases hcov with hgν | hcov
          · exact O.subset (witness := witness) (residual := witness :: rest) (by simp) hνspace hgν
          · have hlenRest : rest.length ≤ fuel := by
              simpa using hlen
            have hlen' : (dropCovered H g rest).length ≤ fuel := by
              exact Nat.le_trans (List.length_filter_le _ rest) hlenRest
            have hspace' : ∀ μ, μ ∈ dropCovered H g rest → μ ∈ space := by
              intro μ hμ
              have hμrest : μ ∈ rest := by
                simp [dropCovered] at hμ
                exact hμ.1
              exact hspace μ (by simp [hμrest])
            have hmem' : ν ∈ dropCovered H g rest := ih hlen' hspace' hνspace hcov
            have hνrest : ν ∈ rest := by
              simp [dropCovered] at hmem'
              exact hmem'.1
            exact by simp [hνrest]

theorem splitGuards_sound {space : List Valuation} {H : GuardLang} (O : SplitOracle space H) :
    ∀ {residual ν},
      (∀ μ, μ ∈ residual → μ ∈ space) →
      ν ∈ space →
      GuardCovered H (splitGuards O residual) ν →
      ν ∈ residual := by
  intro residual ν hspace hνspace hcov
  unfold splitGuards at hcov
  exact splitGuardsFuel_sound O (fuel := residual.length) (Nat.le_refl _) hspace hνspace hcov

theorem evalRows_emittedRow {space : List Valuation} {H : GuardLang} (ρ : Row) :
    ∀ (gs : List H.Guard) (ν : Valuation),
      evalRows (gs.map (emittedRow space H ρ)) ν =
        if RowsMatch space H gs ν then some (ρ.act, ρ.out) else none := by
  intro gs
  induction gs with
  | nil =>
      intro ν
      simp [RowsMatch, evalRows]
  | cons g gs ih =>
      intro ν
      by_cases hg : ν ∈ space ∧ H.holds g ν
      · simp [RowsMatch, evalRows, emittedRow, Row.eval, hg]
      · simp [RowsMatch, evalRows, emittedRow, Row.eval, hg, ih ν]

theorem rowsMatch_splitGuards_iff {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    {ρ : Row} {φ : Formula} {ν : Valuation} :
    RowsMatch space H (splitGuards O (residualVals space ρ φ)) ν ↔
      ν ∈ space ∧ ρ.guard ν ∧ φ ν := by
  constructor
  · intro hmatch
    rcases hmatch with ⟨g, hgmem, hνspace, hgν⟩
    have hres :
        ν ∈ residualVals space ρ φ :=
      splitGuards_sound O
        (residual := residualVals space ρ φ)
        (ν := ν)
        (fun μ hμ => residualVals_mem_space hμ)
        hνspace
        ⟨g, hgmem, hgν⟩
    exact mem_residualVals_iff.mp hres
  · intro hν
    have hres : ν ∈ residualVals space ρ φ := mem_residualVals_iff.mpr hν
    rcases splitGuards_complete O
        (residual := residualVals space ρ φ)
        (ν := ν)
        (fun μ hμ => residualVals_mem_space hμ)
        hres with ⟨g, hgmem, hgν⟩
    exact ⟨g, hgmem, hν.1, hgν⟩

theorem splitTable_eval {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (ρ : Row) (φ : Formula) (ν : Valuation) :
    (splitTable O ρ φ).eval ν =
      if ν ∈ space ∧ ρ.guard ν ∧ φ ν then some (ρ.act, ρ.out) else none := by
  unfold splitTable Table.eval
  rw [evalRows_emittedRow (space := space) (H := H) ρ]
  by_cases hmatch : RowsMatch space H (splitGuards O (residualVals space ρ φ)) ν
  · have hν : ν ∈ space ∧ ρ.guard ν ∧ φ ν := (rowsMatch_splitGuards_iff O).mp hmatch
    simp [hmatch, hν]
  · have hν : ¬ (ν ∈ space ∧ ρ.guard ν ∧ φ ν) := by
      intro hν
      exact hmatch ((rowsMatch_splitGuards_iff O).mpr hν)
    simp [hmatch, hν]

theorem splitTable_eval_on_space {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    {ρ : Row} {φ : Formula} {ν : Valuation} (hν : ν ∈ space) :
    (splitTable O ρ φ).eval ν =
      if ρ.guard ν ∧ φ ν then some (ρ.act, ρ.out) else none := by
  rw [splitTable_eval O ρ φ ν]
  by_cases hcond : ρ.guard ν ∧ φ ν <;> simp [hν, hcond]

theorem split_sound {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    {ρ : Row} {φ : Formula} {ν : Valuation} {out : Action × Valuation} (hν : ν ∈ space) :
    (splitTable O ρ φ).run ν out ↔
      denote (semEnv (fun _ => Table.empty))
        (erase (IProgram.filter φ (IProgram.lit (Table.unit ρ)))) ν out := by
  have hEq :
      (splitTable O ρ φ).eval ν =
        denoteOpt (fun _ => Table.empty) (IProgram.filter φ (IProgram.lit (Table.unit ρ))) ν := by
    rw [splitTable_eval_on_space O hν]
    by_cases hφ : φ ν <;> by_cases hρ : ρ.guard ν <;>
      simp [denoteOpt, unit_eval, Row.eval, hφ, hρ]
  rw [run_iff_eval, hEq]
  exact denoteOpt_some_iff (fun _ => Table.empty) _ _ _

def Table.outputsWithin (space : List Valuation) (T : Table) : Prop :=
  ∀ ρ ∈ T.rows, ρ.out ∈ space

def IProgram.outputsWithin (space : List Valuation) (σ : TableVar → Table) : IProgram → Prop
  | .lit T => T.outputsWithin space
  | .var t => (σ t).outputsWithin space
  | .filter _ C => C.outputsWithin space σ
  | .seq C₁ C₂ => C₁.outputsWithin space σ ∧ C₂.outputsWithin space σ
  | .join C₁ C₂ => C₁.outputsWithin space σ ∧ C₂.outputsWithin space σ
  | .pref C₁ C₂ => C₁.outputsWithin space σ ∧ C₂.outputsWithin space σ

theorem evalRows_output_mem {space : List Valuation} :
    ∀ {rs : List Row}, (∀ ρ ∈ rs, ρ.out ∈ space) → ∀ {ν out},
      evalRows rs ν = some out →
      out.2 ∈ space := by
  intro rs
  induction rs with
  | nil =>
      intro _hrows ν out heval
      simp [evalRows] at heval
  | cons ρ rs ih =>
      intro hrows ν out heval
      by_cases hρ : ρ.guard ν
      · simp [evalRows, Row.eval, hρ] at heval
        cases heval
        exact hrows ρ (by simp)
      · simp [evalRows, Row.eval, hρ] at heval
        have hrows' : ∀ ρ' ∈ rs, ρ'.out ∈ space := by
          intro ρ' hmem
          exact hrows ρ' (by simp [hmem])
        exact ih hrows' heval

theorem Table.eval_output_mem {space : List Valuation} {T : Table} (hT : T.outputsWithin space)
    {ν out} (heval : T.eval ν = some out) : out.2 ∈ space := by
  exact evalRows_output_mem hT heval

theorem splitTable_outputsWithin {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    {ρ : Row} {φ : Formula} (hρ : ρ.out ∈ space) :
    (splitTable O ρ φ).outputsWithin space := by
  intro ρ' hmem
  simp [splitTable, emittedRow] at hmem
  rcases hmem with ⟨g, hg, rfl⟩
  exact hρ

theorem bindSplit_outputsWithin {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (φ : Formula) :
    ∀ {rs : List Row},
      (∀ ρ ∈ rs, ρ.out ∈ space) →
      ∀ {ρ'}, ρ' ∈ bindRows rs (fun ρ => splitTable O ρ φ) → ρ'.out ∈ space := by
  intro rs
  induction rs with
  | nil =>
      intro hrows ρ' hmem
      simp [bindRows] at hmem
  | cons ρ rs ih =>
      intro hrows ρ' hmem
      simp [bindRows] at hmem
      cases hmem with
      | inl hleft =>
          have hρ : ρ.out ∈ space := hrows ρ (by simp)
          exact splitTable_outputsWithin O hρ _ hleft
      | inr hright =>
          apply ih
          · intro ρ'' hmem'
            exact hrows ρ'' (by simp [hmem'])
          · exact hright

theorem Table.bindSplit_outputsWithin {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    {T : Table} (hT : T.outputsWithin space) (φ : Formula) :
    (T.bind (fun ρ => splitTable O ρ φ)).outputsWithin space := by
  intro ρ hmem
  exact Proofs.bindSplit_outputsWithin (O := O) (φ := φ) hT hmem

theorem after_outputsWithin {space : List Valuation} {T₁ T₂ : Table}
    (h₁ : T₁.outputsWithin space) (h₂ : T₂.outputsWithin space) :
    (T₁.after T₂).outputsWithin space := by
  intro ρ hmem
  simp [Table.after] at hmem
  cases hmem with
  | inl hmem1 => exact h₁ _ hmem1
  | inr hmem2 => exact h₂ _ hmem2

theorem seqRows_outputsWithin {space : List Valuation} {rs : List Row} {T₂ : Table} {rows' : List Row}
    (hT₂ : T₂.outputsWithin space) (hseq : seqRows rs T₂ = some rows') :
    ∀ ρ ∈ rows', ρ.out ∈ space := by
  induction rs generalizing rows' with
  | nil =>
      simp [seqRows] at hseq
      cases hseq
      intro ρ hmem
      simp at hmem
  | cons ρ rs ih =>
      cases hEval : T₂.eval ρ.out with
      | none =>
          simp [seqRows, hEval] at hseq
      | some out =>
          cases hRest : seqRows rs T₂ with
          | none =>
              simp [seqRows, hEval, hRest] at hseq
          | some rest =>
              simp [seqRows, hEval, hRest] at hseq
              cases hseq
              intro ρ' hmem
              simp at hmem
              cases hmem with
              | inl hEq =>
                  cases hEq
                  exact Table.eval_output_mem hT₂ hEval
              | inr hmemRest =>
                  exact ih hRest _ hmemRest

theorem compileSeqTable_outputsWithin {space : List Valuation} {T₁ T₂ T : Table}
    (hT₂ : T₂.outputsWithin space) (hcomp : compileSeqTable T₁ T₂ = some T) :
    T.outputsWithin space := by
  unfold compileSeqTable at hcomp
  cases hrows : seqRows T₁.rows T₂ with
  | none =>
      simp [hrows] at hcomp
  | some rows =>
      simp [hrows] at hcomp
      cases hcomp
      exact seqRows_outputsWithin hT₂ hrows

theorem joinRows_outputsWithin {space : List Valuation}
    (hmerge : ∀ {ν₁ ν₂ : Valuation}, ν₁ ∈ space → ν₂ ∈ space → mergeVal ν₁ ν₂ ∈ space) :
    ∀ {rs₁ rs₂ : List Row},
      (∀ ρ ∈ rs₁, ρ.out ∈ space) →
      (∀ ρ ∈ rs₂, ρ.out ∈ space) →
      ∀ {ρ}, ρ ∈ joinRows rs₁ rs₂ → ρ.out ∈ space := by
  intro rs₁
  induction rs₁ with
  | nil =>
      intro rs₂ h₁ h₂ ρ hmem
      simp [joinRows] at hmem
  | cons ρ₁ rs₁ ih =>
      intro rs₂ h₁ h₂ ρ hmem
      simp [joinRows] at hmem
      cases hmem with
      | inl hblock =>
          rcases hblock with ⟨ρ₂, hρ₂, rfl⟩
          exact hmerge (h₁ ρ₁ (by simp)) (h₂ ρ₂ hρ₂)
      | inr hrest =>
          apply ih
          · intro ρ hmem'
            exact h₁ ρ (by simp [hmem'])
          · exact h₂
          · exact hrest

def compileSplit {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (σ : TableVar → Table) : IProgram → Option Table
  | .lit T => some T
  | .var t => some (σ t)
  | .filter φ C => do
      let T ← compileSplit O σ C
      pure <| T.bind (fun ρ => splitTable O ρ φ)
  | .seq C₁ C₂ => do
      let T₁ ← compileSplit O σ C₁
      let T₂ ← compileSplit O σ C₂
      compileSeqTable T₁ T₂
  | .join C₁ C₂ => do
      let T₁ ← compileSplit O σ C₁
      let T₂ ← compileSplit O σ C₂
      pure ⟨joinRows T₁.rows T₂.rows⟩
  | .pref C₁ C₂ => do
      let T₁ ← compileSplit O σ C₁
      let T₂ ← compileSplit O σ C₂
      pure <| T₁.after T₂

theorem bindSplit_evalRows {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (φ : Formula) :
    ∀ (rs : List Row) (ν : Valuation),
      ν ∈ space →
      evalRows (bindRows rs (fun ρ => splitTable O ρ φ)) ν =
        if φ ν then evalRows rs ν else none := by
  intro rs
  induction rs with
  | nil =>
      intro ν hν
      simp [bindRows, evalRows]
  | cons ρ rs ih =>
      intro ν hν
      simp [bindRows, evalRows_append]
      change
        (match (splitTable O ρ φ).eval ν with
          | some out => some out
          | none => evalRows (bindRows rs fun ρ => splitTable O ρ φ) ν) =
        if φ ν then evalRows (ρ :: rs) ν else none
      rw [splitTable_eval_on_space O hν, ih ν hν]
      by_cases hφ : φ ν <;> by_cases hρ : ρ.guard ν <;> simp [evalRows, Row.eval, hφ, hρ]

theorem bindSplit_eval {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (T : Table) (φ : Formula) (ν : Valuation) (hν : ν ∈ space) :
    (T.bind (fun ρ => splitTable O ρ φ)).eval ν =
      if φ ν then T.eval ν else none := by
  simpa [Table.bind, Table.eval] using bindSplit_evalRows O φ T.rows ν hν

theorem compileSplit_outputsWithin {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (hmerge : ∀ {ν₁ ν₂ : Valuation}, ν₁ ∈ space → ν₂ ∈ space → mergeVal ν₁ ν₂ ∈ space)
    (σ : TableVar → Table) :
    ∀ {C T},
      C.outputsWithin space σ →
      compileSplit O σ C = some T →
      T.outputsWithin space := by
  intro C
  induction C with
  | lit T =>
      intro T' hclosed hcomp
      simp [compileSplit] at hcomp
      cases hcomp
      exact hclosed
  | var t =>
      intro T hclosed hcomp
      simp [compileSplit] at hcomp
      cases hcomp
      exact hclosed
  | filter φ C ih =>
      intro T hclosed hcomp
      cases hC : compileSplit O σ C with
      | none =>
          simp [compileSplit, hC] at hcomp
      | some TC =>
          simp [compileSplit, hC] at hcomp
          cases hcomp
          exact Table.bindSplit_outputsWithin O (ih hclosed hC) φ
  | seq C₁ C₂ ih₁ ih₂ =>
      intro T hclosed hcomp
      rcases hclosed with ⟨h₁closed, h₂closed⟩
      cases h₁ : compileSplit O σ C₁ with
      | none =>
          simp [compileSplit, h₁] at hcomp
      | some T₁ =>
          cases h₂ : compileSplit O σ C₂ with
          | none =>
              simp [compileSplit, h₁, h₂] at hcomp
          | some T₂ =>
              cases hseq : compileSeqTable T₁ T₂ with
              | none =>
                  simp [compileSplit, h₁, h₂, hseq] at hcomp
              | some TC =>
                  simp [compileSplit, h₁, h₂, hseq] at hcomp
                  cases hcomp
                  exact compileSeqTable_outputsWithin (ih₂ h₂closed h₂) hseq
  | join C₁ C₂ ih₁ ih₂ =>
      intro T hclosed hcomp
      rcases hclosed with ⟨h₁closed, h₂closed⟩
      cases h₁ : compileSplit O σ C₁ with
      | none =>
          simp [compileSplit, h₁] at hcomp
      | some T₁ =>
          cases h₂ : compileSplit O σ C₂ with
          | none =>
              simp [compileSplit, h₁, h₂] at hcomp
          | some T₂ =>
              simp [compileSplit, h₁, h₂] at hcomp
              cases hcomp
              intro ρ hmem
              exact joinRows_outputsWithin hmerge (ih₁ h₁closed h₁) (ih₂ h₂closed h₂) hmem
  | pref C₁ C₂ ih₁ ih₂ =>
      intro T hclosed hcomp
      rcases hclosed with ⟨h₁closed, h₂closed⟩
      cases h₁ : compileSplit O σ C₁ with
      | none =>
          simp [compileSplit, h₁] at hcomp
      | some T₁ =>
          cases h₂ : compileSplit O σ C₂ with
          | none =>
              simp [compileSplit, h₁, h₂] at hcomp
          | some T₂ =>
              simp [compileSplit, h₁, h₂] at hcomp
              cases hcomp
              exact after_outputsWithin (ih₁ h₁closed h₁) (ih₂ h₂closed h₂)

theorem compileSplit_eval {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (hmerge : ∀ {ν₁ ν₂ : Valuation}, ν₁ ∈ space → ν₂ ∈ space → mergeVal ν₁ ν₂ ∈ space)
    (σ : TableVar → Table) :
    ∀ {C T ν},
      compileSplit O σ C = some T →
      C.outputsWithin space σ →
      ν ∈ space →
      T.eval ν = denoteOpt σ C ν := by
  intro C
  induction C with
  | lit T =>
      intro T' ν hcomp hclosed hν
      simp [compileSplit] at hcomp
      cases hcomp
      rfl
  | var t =>
      intro T ν hcomp hclosed hν
      simp [compileSplit] at hcomp
      cases hcomp
      rfl
  | filter φ C ih =>
      intro T ν hcomp hclosed hν
      cases hC : compileSplit O σ C with
      | none =>
          simp [compileSplit, hC] at hcomp
      | some TC =>
          simp [compileSplit, hC] at hcomp
          cases hcomp
          rw [bindSplit_eval O TC φ ν hν, ih hC hclosed hν]
          by_cases hφ : φ ν <;> simp [denoteOpt, hφ]
  | seq C₁ C₂ ih₁ ih₂ =>
      intro T ν hcomp hclosed hν
      rcases hclosed with ⟨h₁closed, h₂closed⟩
      cases h₁ : compileSplit O σ C₁ with
      | none =>
          simp [compileSplit, h₁] at hcomp
      | some T₁ =>
          cases h₂ : compileSplit O σ C₂ with
          | none =>
              simp [compileSplit, h₁, h₂] at hcomp
          | some T₂ =>
              cases hseq : compileSeqTable T₁ T₂ with
              | none =>
                  simp [compileSplit, h₁, h₂, hseq] at hcomp
              | some TC =>
                  simp [compileSplit, h₁, h₂, hseq] at hcomp
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
                  rw [ih₁ h₁ h₁closed hν]
                  cases hmid : denoteOpt σ C₁ ν with
                  | none =>
                      simp [denoteOpt, hmid]
                  | some mid =>
                      have hT₁closed : T₁.outputsWithin space :=
                        compileSplit_outputsWithin O hmerge σ h₁closed h₁
                      have hmidSpace : mid.2 ∈ space := by
                        have hEval : T₁.eval ν = some mid := by
                          rw [ih₁ h₁ h₁closed hν]
                          exact hmid
                        exact Table.eval_output_mem hT₁closed hEval
                      simp [denoteOpt, hmid]
                      rw [ih₂ h₂ h₂closed hmidSpace]
  | join C₁ C₂ ih₁ ih₂ =>
      intro T ν hcomp hclosed hν
      rcases hclosed with ⟨h₁closed, h₂closed⟩
      cases h₁ : compileSplit O σ C₁ with
      | none =>
          simp [compileSplit, h₁] at hcomp
      | some T₁ =>
          cases h₂ : compileSplit O σ C₂ with
          | none =>
              simp [compileSplit, h₁, h₂] at hcomp
          | some T₂ =>
              simp [compileSplit, h₁, h₂] at hcomp
              cases hcomp
              rw [Table.eval, joinRows_eval]
              have hE₁ : T₁.eval ν = denoteOpt σ C₁ ν := ih₁ h₁ h₁closed hν
              have hE₂ : T₂.eval ν = denoteOpt σ C₂ ν := ih₂ h₂ h₂closed hν
              change
                (match T₁.eval ν, T₂.eval ν with
                  | some out₁, some out₂ => some (Action.pair out₁.1 out₂.1, mergeVal out₁.2 out₂.2)
                  | _, _ => none) =
                (match denoteOpt σ C₁ ν, denoteOpt σ C₂ ν with
                  | some out₁, some out₂ => some (Action.pair out₁.1 out₂.1, mergeVal out₁.2 out₂.2)
                  | _, _ => none)
              rw [hE₁, hE₂]
  | pref C₁ C₂ ih₁ ih₂ =>
      intro T ν hcomp hclosed hν
      rcases hclosed with ⟨h₁closed, h₂closed⟩
      cases h₁ : compileSplit O σ C₁ with
      | none =>
          simp [compileSplit, h₁] at hcomp
      | some T₁ =>
          cases h₂ : compileSplit O σ C₂ with
          | none =>
              simp [compileSplit, h₁, h₂] at hcomp
          | some T₂ =>
              simp [compileSplit, h₁, h₂] at hcomp
              cases hcomp
              rw [after_eval, ih₁ h₁ h₁closed hν, ih₂ h₂ h₂closed hν]
              cases h : denoteOpt σ C₁ ν <;> simp [denoteOpt, h]

theorem compileSplit_refinement {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (hmerge : ∀ {ν₁ ν₂ : Valuation}, ν₁ ∈ space → ν₂ ∈ space → mergeVal ν₁ ν₂ ∈ space)
    {σ : TableVar → Table} {C : IProgram} {T : Table} (hcomp : compileSplit O σ C = some T)
    (hclosed : C.outputsWithin space σ) :
    ∀ {ν : Valuation} {out : Action × Valuation},
      ν ∈ space →
      T.run ν out →
      denote (semEnv σ) (erase C) ν out := by
  intro ν out hν hrun
  have heval : T.eval ν = some out := hrun
  rw [compileSplit_eval O hmerge σ hcomp hclosed hν] at heval
  exact (denoteOpt_some_iff σ C ν out).1 heval

theorem compileSplit_complete {space : List Valuation} {H : GuardLang} (O : SplitOracle space H)
    (hmerge : ∀ {ν₁ ν₂ : Valuation}, ν₁ ∈ space → ν₂ ∈ space → mergeVal ν₁ ν₂ ∈ space)
    {σ : TableVar → Table} {C : IProgram} {T : Table} (hcomp : compileSplit O σ C = some T)
    (hclosed : C.outputsWithin space σ) :
    ∀ {ν : Valuation} {out : Action × Valuation},
      ν ∈ space →
      denote (semEnv σ) (erase C) ν out →
      T.run ν out := by
  intro ν out hν hden
  have heval : denoteOpt σ C ν = some out := (denoteOpt_some_iff σ C ν out).2 hden
  show T.eval ν = some out
  rw [compileSplit_eval O hmerge σ hcomp hclosed hν]
  exact heval

def SatisfiesOnSpace (space : List Valuation) (f : RelSem) (Φ : GFD) : Prop :=
  ∀ ⦃ν₁ ν₂ : Valuation⦄,
    ν₁ ∈ space →
    ν₂ ∈ space →
    Φ.guard ν₁ →
    Φ.guard ν₂ →
    agreesOn Φ.xs ν₁ ν₂ →
    Defined f ν₁ ∧
    Defined f ν₂ ∧
    (∀ out, f ν₁ out → supportWithin Φ.ys out.2 ∧ Φ.post out.2) ∧
    (∀ out, f ν₂ out → supportWithin Φ.ys out.2 ∧ Φ.post out.2) ∧
    ∀ out₁ out₂, f ν₁ out₁ → f ν₂ out₂ → out₁ = out₂

theorem compileSplit_domain_preservation {space : List Valuation} {H : GuardLang}
    (O : SplitOracle space H)
    (hmerge : ∀ {ν₁ ν₂ : Valuation}, ν₁ ∈ space → ν₂ ∈ space → mergeVal ν₁ ν₂ ∈ space)
    {σ : TableVar → Table} {Δ : TableVar → Formula}
    (hΔ : EnvModelsDomT σ Δ) {C : IProgram} {φ : Formula} {ν : Valuation}
    (hdom : DomCheck Δ (erase C) φ) {T : Table}
    (hcomp : compileSplit O σ C = some T)
    (hclosed : C.outputsWithin space σ)
    (hν : ν ∈ space) :
    Defined T.run ν → φ ν := by
  intro hdef
  exact domain_overapprox hΔ hdom <| by
    rcases hdef with ⟨out, hout⟩
    exact ⟨out, compileSplit_refinement O hmerge hcomp hclosed hν hout⟩

theorem compileSplit_type_preservation {space : List Valuation} {H : GuardLang}
    (O : SplitOracle space H)
    (hmerge : ∀ {ν₁ ν₂ : Valuation}, ν₁ ∈ space → ν₂ ∈ space → mergeVal ν₁ ν₂ ∈ space)
    {σ : TableVar → Table} {Γ : TableVar → List GFD} {Δ : TableVar → Formula}
    (hΓ : EnvModelsFDT σ Γ) (hΔ : EnvModelsDomT σ Δ)
    {C : IProgram} {Φ : GFD} (hfd : FDCheck Γ Δ (erase C) Φ) {T : Table}
    (hcomp : compileSplit O σ C = some T)
    (hclosed : C.outputsWithin space σ) :
    SatisfiesOnSpace space T.run Φ := by
  intro ν₁ ν₂ hν₁ hν₂ hg₁ hg₂ hag
  rcases type_soundness hΓ hΔ hfd hg₁ hg₂ hag with ⟨hdef₁, hdef₂, hpost₁, hpost₂, huniq⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hdef₁ with ⟨out, hout⟩
    exact ⟨out, compileSplit_complete O hmerge hcomp hclosed hν₁ hout⟩
  · rcases hdef₂ with ⟨out, hout⟩
    exact ⟨out, compileSplit_complete O hmerge hcomp hclosed hν₂ hout⟩
  · intro out hout
    exact hpost₁ _ (compileSplit_refinement O hmerge hcomp hclosed hν₁ hout)
  · intro out hout
    exact hpost₂ _ (compileSplit_refinement O hmerge hcomp hclosed hν₂ hout)
  · intro out₁ out₂ hout₁ hout₂
    exact huniq _ _ (compileSplit_refinement O hmerge hcomp hclosed hν₁ hout₁)
      (compileSplit_refinement O hmerge hcomp hclosed hν₂ hout₂)

def EquivalentModuloOnSpace (space : List Valuation) (σ : TableVar → Table)
    (C : IProgram) (T : Table) (Φ : GFD) : Prop :=
  ∀ ⦃ν₁ ν₂ : Valuation⦄ ⦃out₁ out₂ : Action × Valuation⦄,
    ν₁ ∈ space →
    ν₂ ∈ space →
    Φ.guard ν₁ →
    Φ.guard ν₂ →
    agreesOn Φ.xs ν₁ ν₂ →
    denote (semEnv σ) (erase C) ν₁ out₁ →
    T.run ν₂ out₂ →
    out₁ = out₂

theorem compileSplit_correctness {space : List Valuation} {H : GuardLang}
    (O : SplitOracle space H)
    (hmerge : ∀ {ν₁ ν₂ : Valuation}, ν₁ ∈ space → ν₂ ∈ space → mergeVal ν₁ ν₂ ∈ space)
    {σ : TableVar → Table} {Γ : TableVar → List GFD} {Δ : TableVar → Formula}
    (hΓ : EnvModelsFDT σ Γ) (hΔ : EnvModelsDomT σ Δ)
    {C : IProgram} {Φ : GFD} (hfd : FDCheck Γ Δ (erase C) Φ) {T : Table}
    (hcomp : compileSplit O σ C = some T)
    (hclosed : C.outputsWithin space σ) :
    EquivalentModuloOnSpace space σ C T Φ := by
  intro ν₁ ν₂ out₁ out₂ hν₁ hν₂ hg₁ hg₂ hag h₁ h₂
  rcases compileSplit_type_preservation O hmerge hΓ hΔ hfd hcomp hclosed hν₁ hν₂ hg₁ hg₂ hag with
    ⟨_, _, _, _, huniq⟩
  exact huniq _ _ (compileSplit_complete O hmerge hcomp hclosed hν₁ h₁) h₂

end

end Proofs
