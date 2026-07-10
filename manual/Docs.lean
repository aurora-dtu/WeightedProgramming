import VersoManual
import WeightedProgramming

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.exampleModule "Wnetkat.Wspp.Defs"

set_option verso.docstring.allowMissing true

open scoped Computability

structure PaperConfig : Type where
  full : Option Lean.Name

section
open Lean Verso ArgParse Scopes Elab

variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadLiftT TermElabM m]

def PaperConfig.parse : ArgParse m PaperConfig :=
  PaperConfig.mk <$> ((fun _ => none) <$> .done <|> .positional `name ref)
where
  ref : ValDesc m (Option Name) := {
    description := "reference name"
    signature := .Ident
    get := fun
      | .name x =>
        try
          let resolved ← liftM (runWithOpenDecls (runWithVariables fun _ => realizeGlobalConstNoOverloadWithInfo x))
          return some resolved
        catch
          | .error ref e => throwErrorAt ref e
          | _ => return none
      | other => throwError "Expected reference name, got {repr other}"
  }

instance : FromArgs PaperConfig m := ⟨PaperConfig.parse⟩
end

section

open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets ExpectString
open Lean Elab

open SubVerso.Highlighting

open Verso.SyntaxUtils (runParserCategory' SyntaxError parseStrLitAsCategory strLitInputContext)

open Lean.Doc.Syntax
open Lean.Elab.Tactic.GuardMsgs

open Qq
open Verso.Doc.Elab

@[role]
def paper : RoleExpanderOf PaperConfig
  | cfg, #[arg] => do
    let `(inline|code( $name:str )) := arg
    | throwErrorAt arg "Expected code literal with the example name"
    let exampleName := name.getString.toName
    let identStx := mkIdentFrom arg (cfg.full.getD exampleName) (canonical := true)
    let e ← Lean.Elab.Term.elabTermAndSynthesize identStx none
    let e ← instantiateMVars e
    let e ← Meta.mkAppM ``Lean.toExpr #[e]
    let e ← unsafe Lean.Meta.evalExpr Expr q(Expr) e (safety := .unsafe)

    ``(Inline.bold #[Inline.text $(quote (e.dbgToString.drop 1 |>.dropEnd 1).toString)])
  | _, _ => `(Inline)

end

namespace Labels

def Def (n : String) := s!"Definition {n}"
/-- This is mostly to ensure that we haven't missed any numbers -/
def Exm (n : String) := s!"Example {n}"
def Thm (n : String) := s!"Theorem {n}"
def Lem (n : String) := s!"Lemma {n}"
def Cor (n : String) := s!"Corollary {n}"

open Verso.Genre
open Verso.Doc.Concrete

/-! ## Papers -/

def pldi26 : InProceedings where
  title := inlines!"Weighted NetKAT: A Programming Language for Quantitative Network Verification"
  authors := #[inlines!"Emmanuel Suárez Acevedo", inlines!"Tiago Ferreira", inlines!"Kevin Batz", inlines!"Oliver Bøving", inlines!"Nate Foster", inlines!"Alexandra Silva"]
  year := 2026
  booktitle := inlines!"PLDI"

def itp26 : InProceedings where
  title := inlines!"Securing the Foundations of an Intermediate Language for Probabilistic Program Verification"
  authors := #[inlines!"Oliver Bøving", inlines!"Christoph Matheja"]
  year := 2026
  booktitle := inlines!"ITP"

/-! ## Section 2 -/

def def'monoid := Def "2.1"
def exm'3_2 := Exm "2.2"
def def'module := Def "2.4"
def exm'3_4 := Exm "2.4"
def exm'3_5 := Exm "2.5"
def def'naturally_ordered_module := Def "2.6"
def exm'3_7 := Exm "2.7"
def def'cont_module := Def "2.8"
def lem'countable_sums := Lem "2.9"

/-! ## Section 3 -/

def def'weighted_reward_module := Def "3.1"
def exm'4_2 := Exm "3.2"
def def'wGCL := Def "3.3"
def exm'4_4 := Exm "3.4"
def exm'4_5 := Exm "3.5"
def def'scoring := Def "3.6"
def lem'wp_mono := Lem "3.8"
def thm'knaster_tarski := Thm "3.9"
def cor'knaster_tarski_park := Cor "3.10"

/-! ## Section 4 -/

def def'wdp := Def "4.1"
def exm'mpd_is_wdp := Exm "4.2"
def def'toWDP := Def "4.3"
def def'schedulers := Def "4.5"
def def'h_schedulers := Def "A.16"
def def'paths := Def "4.6"
def def'weights := Def "4.7"
def def'wrew := Def "4.8"
def def'op := Def "4.9"
def def'sound_wp_eq_op := Def "4.11"
def def'T_T' := Def "4.12"
def thm'wp_eq_lp := Thm "4.13"

/-! ## Section 5 -/

def lem'T_MinWRew_le_MinWRew := Lem "5.1"
def def'k_inf_distrib := Def "5.4"
def lem'no_lfp_prop := Lem "5.6"
def lem'T_MinWRew_eq_MinWRew := Lem "5.7"
def def'wdp_well_behaved := Def "5.8"
def exm'mdp_wellBehaved := Exm "5.9"
def thm'lfp_T_eq_MinWRew := Thm "5.10"
def thm'WellBehavedModule_pi := Thm "5.12"
def cor'wp_eq_op_of_isProb := Cor "5.24"
def cor'actic_wb := Cor "5.25"
def cor'formal_languages := Cor "5.26"

end Labels

open Labels

open OmegaCompletePartialOrder

#doc (Manual) "Countable Nondeterminism in Weighted Programming with an Application to Mechanized Foundations for Probabilistic Program Verification (Lean manual)" =>
%%%
authors := []
shortTitle := "Countable Nondeterminism in Weighted Programming with an Application to Mechanized Foundations for Probabilistic Program Verification"
%%%

{index}[example]

This is the accompanying Lean manual to the paper _Countable Nondeterminism in Weighted Programming with an Application to Mechanized Foundations for Probabilistic Program Verification_ submitted to POPL'27. The manual is built using [Verso](https://verso.lean-lang.org/), which enabled hoverable code excerpts and generally allows us to integrate the paper and the mechanization.

The source code for the mechanization, which is described in this manual, can be found hosted online anonymously at:

> [https://anonymous.4open.science/r/WeightedProgramming-C43C/](https://anonymous.4open.science/r/WeightedProgramming-C43C/)

The mechanization and this manual was produced and written without the use of LLM's.

# Introduction

_No definitions in this section._

# Preliminaries

:::leanSection

Much of the foundational structures and theories we use, we can inherit from [mathlib](https://mathlib.org/), which we attempt to do as much as possible. However, some of these are _slightly_ different from the requirements we have, which we will make clear as necessary.

{paper}`def'monoid`, which introduces _monoids_, are present in mathlib under {name}`Monoid` (where the operator is `*` and unit is `1`) and {name}`AddMonoid` (where the operator is `+` and unit is `0`). They each have commutative variants {name}`CommMonoid` and {name}`AddCommMonoid`, of which we will use the latter more often.

{paper}`def'module` introduces _modules_, which in mathlib terms is a {name}`MonoidWithZero` with a {name}`AddCommMonoid`.

```lean
variable {𝒲 ℛ : Type} [MonoidWithZero 𝒲] [AddCommMonoid ℛ]
```

The scalar multiplication joining the two are given by {name}`SMul` and it's associative, distributive, annihalation and neutrality properties are given by {name}`DistribMulAction`.

> The below definition is extracted from the lean source code. Click the checkbox next to {lean}`MulAction` under *Extends* to see the full definition.

{docstring DistribMulAction}

Note that we are _not_ using {name}`Module` from mathlib, as that would require {lean}`𝒲` to be a {lean}`Semiring`, which we do not require, while {name}`DistribMulAction` has exactly the properties we want.

We consider only structures {lean}`ℛ` with orders being {name}`CompleteLattice`'s, which provide {name}`sSup` and {name}`sInf` as supremum and infimum over sets. {paper}`def'naturally_ordered_module` defines _naturally ordered_ captured by {name}`CanonicallyOrderedAdd`.

```lean
variable [CompleteLattice ℛ] [CanonicallyOrderedAdd ℛ]
```

{paper}`def'cont_module` defines ω-continuity which we formalize as two type classes {name}`ωScottContinuousAdd` and {name}`ωScottContinuousSMul`. These build on the notion of {name}`ωScottContinuous` from the {name}`OmegaCompletePartialOrder` module (a weaker order than {name}`CompleteLattice` and this we have an instance {inst}`OmegaCompletePartialOrder ℛ`). This bears a connection to continuity in the Scott topology {name}`Topology.scott`, but the only property we rely on is preservation of {name}`ωSup`, the chain/countable analogue of {name}`iSup`.

{paper}`lem'countable_sums` introduces _countable sums_. There is not, at the time of writing, a direct correspondence to this notion of a countable sum defined for {name}`CompleteLattice`'s with {name}`AddCommMonoid` and {name}`CanonicallyOrderedAdd`. The closest is {name}`tsum`, short for topological sum and defined as a topological limit. However, since we do not impose a topological space on our structure, we use an alternative definition based on {name}`ωSup` namely {name}`ωSum`, heavily inspired by Weighted NetKAT's {citep pldi26}[] definition under the same name.

{docstring ωSum}

:::

# Weighted Programming

In this section we introduce {name}`wGCL`, its syntax and its semantics.

{paper}`def'weighted_reward_module` defines a _weighted-reward module_ which we replicate as a collection of type classes.

```lean -show
open WDP
```

```lean
variable {𝒲 ℛ : Type}
  [MonoidWithZero 𝒲] [AddCommMonoid ℛ]
  [DistribMulActionWithZero 𝒲 ℛ]
  -- Order requirements
  [CompleteLattice ℛ] [CanonicallyOrderedAdd ℛ]
  -- Monotonicity of operators
  [AddLeftMono ℛ] [SMulMonoRight 𝒲 ℛ]
  -- Continuity of operators
  [SMulContinuous 𝒲 ℛ] [ωScottContinuousSMul 𝒲 ℛ]
  [AddBicontinuous ℛ] [ωScottContinuousAdd ℛ]
```

Generally we attempt the use the minimal set of requirements per theorem and pick as choose as needed, but for the purpose of this demonstration the above cover most of the requirements for all theorems.

## Program States and Expressions

:::leanSection

```lean -show
variable {D : Type} {Γ : D → Type} {σ : Σ[Γ]} {d : D}
```

We assume a set (a {lean}`Type`) of variables {lean}`(D : Type)` and a typing context {lean}`(Γ : D → Type)` that assign types to all members of {lean}`D`. This is a slight deviation from the paper, which has all variables as {name}`Nat`'s, but for the purpose of the mechanization it was trivial to parameterize the type of the variables; the only requirement is adding a {name}`Countable` constraint in certain places, otherwise the theory remains exactly the same.

We introduce _memories_ over these variables as dependent maps where we write {lean}`(σ : Σ[Γ])` as a shorthand of {lean}`(σ : ((d : D) → Γ d))` saying that {lean}`σ` takes elements {lean}`d` from {lean}`D` and returns a value of type {lean}`Γ d`.

:::

```lean
variable {D : Type} {Γ : D → Type} {σ : Σ[Γ]}
-- Example variable and value
variable {d : D} {v : Γ d}
-- For the purpose of updating memories
variable [DecidableEq D]
```

We introduce notation for _substitution_ through the type class {name}`Substitution`, allowing us to write {lean}`σ[d ↦ v]`, setting the value of {lean}`d` to {lean}`v`.

We _do not_ impose a deep embedding on the expressions of {name}`wGCL`, instead we model these as functions from {lean}`Σ[Γ]` to specific types. Since we have a typing context, these are often dependent on the context, however, some general expressions are:

- Boolean expression: {lean}`Σ[Γ] → Bool`
- Reward expression: {lean}`Σ[Γ] → ℛ`
- Weight expression: {lean}`Σ[Γ] → 𝒲`
- General expression over a variable {lean}`d`: {lean}`Σ[Γ] → Γ d`

For distributions we introduce the type {name}`wGCL.Dist` parametrized over a type.

{docstring wGCL.Dist}

{name}`Substitution` also applies to expressions with the same notation.

## Program Syntax

{paper}`def'wGCL` introduces the syntax of {name}`wGCL`, shown in the definition bewlow.

{docstring wGCL}

> In the formalization we've encoded `if b then C₁ else C₂` by way of the weighted choice with Iverson brackets $`C₁ {}_{[b]}⊕_{[¬b]} C₂`. This is semantically equivalent to the paper definition of `if b then C₁ else C₂`, but eases the proof burden a little bit.

## Weakest Precondition Semantics

```lean -show
open wGCL
```

We define the denotational semantics of {name}`wGCL` in terms of a _backward-moving weakest
prescoring transformer_ {name}`wp`. The transformer is defined as an {name}`OrderHom`, described as a _"Bundled monotone (aka, increasing) function"_, i.e. the proof of monotonicity is shown at time of definition thus showing {paper}`lem'wp_mono`.

{docstring wGCL.wp}

Scorings, as per {paper}`def'scoring` are not defined explicitly, but rather as functions point-wise lifting the properties of their codomain.

{paper}`thm'knaster_tarski` and {paper}`cor'knaster_tarski_park` are covered by mathlibs {name}`OrderHom.lfp` and associated theorems, {name}`OrderHom.lfp_le` (the underpinning of {paper}`cor'knaster_tarski_park`) and {name}`OrderHom.le_lfp` are both used extensively the proofs of following theorems.

# Operational Semantics via Weighted Decision Processes

In this section we introduce an operation semantics for {name}`wGCL` by way of a _weighted decision process_ ({name}`WDP`).

{docstring WDP}

For the purpose of proofs, it turned out to be easier _not_ to bundle the reward function `ρ` with the {name}`WDP`.

```lean
variable {S A : Type} {M : WDP 𝒲 S A}
```

## The Operational Weighted Decision Process

We need to induce a operational {name}`WDP` for {name}`wGCL` where the state space is defined by _configurations_ {name}`Conf`.

{docstring wGCL.Conf}

Along side the configurations, we need to introduce a small-step execution relation {name}`Step` as an inductive data type.

{docstring wGCL.Step}

In addition to this definition, we also introduce {name}`Conf.succs` and {name}`Conf.succsₐ` which rephrase the semantics using a more explicit set construction of successors, shown equivalent by {name}`Conf.succs_agree`. This other formulation helps Lean's automation better identify the complete set of successors, crucial for showing properties such as _countable successors_ {name}`Conf.succs_countable`.

These define a {name}`Conf.τ` a transition function for the {name}`WDP` that is induced by {name}`Step` referred to as {name}`wGCL.toWDP` as per {paper}`def'toWDP`. In these we also define {name}`ρ` and {name}`ρ'` as the scoring functions parametric over postweighting.

## Minimal Weighted Rewards

Following the path of `MDP`'s, we introduce a notion of _schedulers_ as per {paper}`def'schedulers`. This includes two schedulers, {name}`Sched`, and memoryless {name}`MSched`. Additionally we make use of _history length dependent schedulers_ defined in {paper}`def'h_schedulers` named {name}`HSched` that only considers the current state and length of the history.

```lean
variable {𝔖 : M.Sched} {ℒ : M.MSched}
```

```lean -show
variable {n : ℕ} {s₀ : S}
```

From {paper}`def'paths` we define {name}`WDP.Path` as nonempty lists of states. We define {lean}`Path.of n s₀` as the set of parths starting in state {lean}`s₀` with length {lean}`n`, mirroring the syntax $`\text{Paths}^{=n}(s₀)`.

```lean
variable {π : Path S}
```

From {paper}`def'weights` we define {name}`WDP.Path.Weight` computing the product of transition weights between successive states of a given path {lean}`π` and a scheduler {lean}`𝔖`. Since our product is not necessarily commutative we can't use {name}`Finset.prod` and have to resort to {name}`List.prod` with {name}`List.pairs`, however, since we store the latest state in a path as the head, we have to compute this product in reverse and thus rely on {name}`List.rprod`.

We call {lean}`Path.of₀ n s₀ 𝔖` the set of paths of length {lean}`n` starting in state {lean}`s₀` with non-zero weight according to {lean}`𝔖`. The set {name}`Path.of₀`, as opposed to {name}`Path.of` which doesn't consider weights, is _countable_ as shown by {name}`Path.of₀_countable`.

{paper}`def'wrew` defines three notions of _weighted reward_ on {lean}`WDP`'s:

```lean -show
open OrderHom
variable {ρ : S → ℛ}
```

- {name}`WRew`: _weighted reward_ given a length {lean}`n`, an initial state {lean}`s₀`, and, a scheduler {lean}`𝔖`

    {lean}`∑ i ≤ n, ω∑ π : Path.of₀ i s₀ 𝔖, π.val.Weight 𝔖 • ρ π.val.head`

- {name}`WRew'`: weighted _total_ reward given an initial state {lean}`s₀` and a scheduler {lean}`𝔖`

    {lean}`⨆ n : ℕ, M.WRew ρ n 𝔖 s₀`

- {name}`MinWRew`: _minimal_ weighted total reward given an initial state {lean}`s₀`

    {lean}`⨅ 𝔖 : M.Sched, M.WRew' ρ 𝔖 s₀`

{paper}`def'op` phrases {name}`op` the minimal weighted total reward in the shape of an prescoring transformer like {name}`wp`. This definition allows us to compare exactly {name}`op` with {name}`wp`, namely stating that operational and denotational semantics agree, as per {paper}`def'sound_wp_eq_op`. Ultimately this is shown later with {name}`wp_eq_op`.

{docstring wGCL.op}

## Recursive Characterization of Minimal Weighted Rewards

To show {name}`wp_eq_op` we first show a relation on the level of {name}`WDP`'s, relating {name}`MinWRew` to the _least fixed point_ of the _Bellman_ operator as defined in {paper}`def'T_T'`, defining the minimizing Bellman operator {name}`T` and a variant {name}`T'` the uses a fixed memory scheduler {lean}`ℒ`.

To bring {name}`T` into the land of prescoring transformer {name}`lp` is defined as a short hand for {name}`lfp` {name}`T`.

Thus, {paper}`thm'wp_eq_lp` shows {name}`wp_eq_lp`. A lot of grunt work goes into showing this theorem with core definitions being {name}`ξ` and {name}`Φ'` inspired by the mechanization efforts of {citep itp26}[].

# When are minimal weighted rewards (not) equal to least fixed points?

The objective of this section is to characterize the connection between {name}`T` and {name}`MinWRew`, ultimately showing that {name}`lfp` {name}`T` is equal to {name}`MinWRew`. To this end, {paper}`lem'T_MinWRew_le_MinWRew` shows that {name}`MinWRew` is a prefixed of {name}`T`.

{docstring WDP.T_MinWRew_le_MinWRew}

## Module Level: A Necessary Condition for the LFP Property

As we introduced ω-continuity for addition and scaling with {lean}`ωScottContinuousAdd` and {lean}`ωScottContinuousSMul`, we need a similar, but slightly stronger concept for infimums, namely 𝓀-inf-distributivity as described in {paper}`def'k_inf_distrib`. We need to describe distributivity with respect to {name}`iInf`, that is with respect to a index of certain shapes. The paper classifies this property by way of cadinality, however, in the mechanization we chose to require this on the specific type(s) that we take infimums over, formalized by the type class {name}`SMulCocontinuousOn`, most importantly over {name}`Sched`.

{docstring WDP.SMulCocontinuousOn}

_We did not formalize the statement of {paper}`lem'no_lfp_prop`._

{paper}`lem'T_MinWRew_eq_MinWRew` strengthens {paper}`lem'T_MinWRew_le_MinWRew` to show that {name}`MinWRew` is a true fixed point of {name}`T`, {name}`T_MinWRew_eq_MinWRew`, with extra constraints on the module.

{docstring WDP.T_MinWRew_eq_MinWRew}

## WDP Level: A Sufficient Condition for the LFP property

What remains to show is that {name}`MinWRew` is not only a fixed point, but also the _least_. This requires the introduction of _well-behaved {name}`WDP`'s_ as per {paper}`def'wdp_well_behaved`.

{docstring WDP.WellBehaved}

```lean -show
variable {v ρ : S → ℛ} {h : M.T ρ v ≤ v}
```

The above definition is the _structure of a well-behaved {name}`WDP`_ with respect to a specific prefixed point {lean}`v`. The more general type class is {name}`IsWellBehaved` which states that a {name}`WellBehaved` exists for every prefixed point of a given {name}`WDP`.

{docstring WDP.WellBehaved}

{paper}`exm'mdp_wellBehaved` establishes that {name}`WDP`'s with a module of {name}`PReal` scalars over {name}`ENNReal` and sum of successor weight bounded by {lean}`1`, exactly those {name}`WDP`'s that `MDP`'s embed into, are well-behaved as shown with {name}`mdp_wellBehaved`.

Crucially, we can show in {paper}`thm'lfp_T_eq_MinWRew` that {name}`WellBehaved` {name}`WDP`'s satisfy the lfp-property, as shown in {name}`lfp_T_eq_MinWRew`.

Extending the class of {name}`WDP`'s from specific to _all those with a specific module_ we introduce the concept of a {name}`WellBehavedModule`.

{docstring WDP.WellBehavedModule}

The notion of well-behaved modules extends to arbitrary products of well-behaved modules as per {paper}`thm'WellBehavedModule_pi` and {name}`WellBehavedModule.pi`.

## Transporting the LFP Property through Normalization

_This section and normalization has not been mechanized in Lean._

## Classes of WDPs with the Least Fixed Point Property

We show that {name}`wGCL` programs over certain modules and with particular structures produce well-behaved {name}`WDP`'s. In particular we show that {name}`PReal`-{name}`ENNReal` modules with programs consisting of weighted choices limited to $`C₁ {}_{p}⊕_{1-p} C₂` admit well-behaved {name}`WDP`'s ultimately showing {name}`wp_eq_op_of_isProb` reflecting {paper}`cor'wp_eq_op_of_isProb`.

_{paper}`cor'actic_wb` and {paper}`cor'formal_languages` concerning the Arctic semiring and Formal languages semiring respectively has not been formalized._

# Case Studies

_This section has not been mechanized in Lean._

# Related Work

_No definitions in this section._

# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
