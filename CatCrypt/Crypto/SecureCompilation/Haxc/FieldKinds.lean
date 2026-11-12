/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.HtermOfKinds

/-!
# Kind signatures of prime-field code and canonical array inputs

The constant-time theorem `haxc_ct_proved_all` of `compileA` takes the run hypothesis
`hterm`: the body the front reads runs to a value from the entry environment of every
valuation the layout reads off an entry state. For code over the tagged field heads at a
modulus `p` (`add#p…`, `sub#p…`, `mul#p…`), a head answers only on canonical
representatives, below `p`. This module gives kind signatures that track canonical
representatives and derives the run hypothesis from one run of the kind checker
`Hax.Total.KindSig.check`.

* For scalar parameters, `fieldKindSig p heads` types each head of `heads` on two integer
  ranges inside `[0, p - 1]` with the range `[0, p - 1]`; the register bounds of the layout
  (`entryKindsB`) make every entry value canonical. The loop rule of the checker requires a
  value carried through a loop to keep its kind, and a field head keeps the range
  `[0, p - 1]` (`fieldKindSig_check_carried`).
* For array parameters, the kind `CKind.carr n` is an array of `n` canonical words; the
  signature `canonKindSig p S` adds to a word signature `S` the rules of `index` and
  `array_update` on such arrays. The precondition `canonPre σ p` on entry states states that
  every scalar parameter's register and every word of every array parameter is below `p`;
  under it the entry environment of every layout binds its parameters at the kinds
  `entryKindsC σ p` (`envOK_entryEnvOf_of_canonPre`), with no register bound.

## Main definitions

* `fieldKindSig` — the kind signature of straight-line code over tagged field heads.
* `kindSigOr`, `mulSizeW`, `fieldWordSig` — a signature extended by further heads; the
  checked `usize` product; the field heads with the word operations and `Mul#size`.
* `CKind`, `cOfKind`, `canonKindSig` — word kinds and arrays of canonical words, their
  values, and the signature with the array rules.
* `argKindC`, `entryKindsC`, `canonPre` — the kinds of the parameters under canonical
  entries, and the precondition of canonical entries.

## Main results

* `fieldKindSig_sound`, `run_val_of_fieldCheck`, `ct_of_fieldCheck` — the run hypothesis
  and constant time of `compileA` from the checker at `fieldKindSig p heads`.
* `fieldKindSig_check_carried` — a value carried through a counted loop and rebound to a
  field product keeps the range `[0, p - 1]`.
* `canonKindSig_sound`, `fieldWordSig_sound` — soundness for `hax64WExit`.
* `envOK_entryEnvOf_canon`, `envOK_entryEnvOf_of_canonPre` — the entry environment binds
  the parameters at their canonical kinds, for every layout.
* `run_val_of_canonCheck`, `ct_of_fieldCheckPre` — the run hypothesis and constant time of
  `compileA` between entry states satisfying `canonPre`, from the checker at
  `canonKindSig p S`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.Haxc.CTTotality (WKind wKindSig wOfKind wKindSig_sound
  hax64WExit_word)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog varIndex)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapCtx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (RunL)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTimeRel)
open CatCrypt.Crypto.Hax.NFToCat (mapVal catTy abiKindArr abiParamsArr)
open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnvOf crateBi)
open CatCrypt.Crypto.Hax (HaxModule hax64WExit hax64WExit_of_ne hax64Exit
  not_hax64WideHead_of_lt exitScalarRes hax64ScalarOp exitMarshalOk towerOfCallName
  hax64ScalarAdmit hax64ArgsShape hax64IntArgs scalarValNB)
open _root_.Hax (Value denote')
open _root_.Hax.Total (KindSig)
open _root_.Hax.FieldTag (FieldMethod fieldTag? fieldVal fieldVal_lt fieldArgs fieldArm)

/-! ## Straight-line field code -/

/-- The kind signature of straight-line code over the tagged field heads `heads` at the
    modulus `p`: the literals, ranges and loop counters of `wKindSig`, and each head of
    `heads` takes two integers in ranges inside `[0, p - 1]` to an integer in that range. -/
def fieldKindSig (p : ℕ) (heads : List String) : KindSig WKind :=
  { wKindSig with
    sig := fun f ks =>
      match ks with
      | [.rng a b, .rng c d] =>
        if f ∈ heads ∧ 0 ≤ a ∧ 0 ≤ c ∧ b < p ∧ d < p then some (.rng 0 ((p : Int) - 1))
        else none
      | _ => none }

/-- **Soundness of the field signature.** If each head of `heads` answers two canonical
    representatives with a canonical representative under `hax64WExit`, the signature
    `fieldKindSig p heads` is sound for `wOfKind` and `hax64WExit`. -/
theorem fieldKindSig_sound {p : ℕ} {heads : List String}
    (hheads : ∀ f ∈ heads, ∀ a b : ℕ, a < p → b < p →
      ∃ c : ℕ, hax64WExit f [.int a, .int b] = some (.int c) ∧ c < p) :
    (fieldKindSig p heads).Sound wOfKind hax64WExit where
  noCF := wKindSig_sound.noCF
  lit := wKindSig_sound.lit
  range := wKindSig_sound.range
  ctr := wKindSig_sound.ctr
  sig f ks k h vs hvs := by
    simp only [fieldKindSig] at h
    split at h
    · next a b c d =>
      split_ifs at h with hc
      cases h
      obtain ⟨hf, ha, hc0, hb, hd⟩ := hc
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
        simp only [KindSig.KindsOK, and_false] at hvs
      obtain ⟨⟨x, rfl, hx1, hx2⟩, ⟨y, rfl, hy1, hy2⟩, -⟩ := hvs
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ x)
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ y)
      obtain ⟨r, hr, hrp⟩ := hheads f hf n m (by omega) (by omega)
      exact ⟨_, hr, r, rfl, by omega, by omega⟩
    · cases h

/-- A tagged binary field head at a modulus `0 < p < 2 ^ 64` answers two canonical
    representatives with a canonical representative under `hax64WExit`. -/
theorem hax64WExit_field_canon {p : ℕ} (hp0 : 0 < p) (hp : p < 2 ^ 64) {f : String}
    {m : FieldMethod} (ht : fieldTag? f = some (m, p)) (hm : m.binary = true)
    (h1 : f ≠ "array_lit") (h2 : f ≠ "repeat") (h3 : f ≠ "eq#arr") (h4 : f ≠ "ne#arr")
    (h5 : f ≠ "len") (h6 : f ≠ "Not") (hres : exitScalarRes f = true)
    (hop : hax64ScalarOp f = false) (hto : exitMarshalOk (towerOfCallName f) = true)
    {a b : Nat} (ha : a < p) (hb : b < p) :
    ∃ c : Nat, hax64WExit f [.int a, .int b] = some (.int c) ∧ c < p := by
  rw [hax64WExit_of_ne h1 h2 h3 h4 (not_hax64WideHead_of_lt ht hp)
    (CatCrypt.Crypto.Hax.ne_select_of_exitScalarRes hres)]
  have hbi := _root_.Hax.hax64Builtins_fieldArgs ht hp a b
  simp only [fieldArgs, hm, ite_true, fieldArm, ha, hb, true_and, forall_const] at hbi
  refine ⟨fieldVal m p a b, ?_, fieldVal_lt m hp0 a b⟩
  have hc := fieldVal_lt m hp0 a b
  have hsh : hax64ArgsShape f [.int a, .int b] = true := by
    unfold hax64ArgsShape
    rw [hop, ite_eq_right (by simp), ite_eq_right h6]
    simp only [hax64IntArgs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq]
    omega
  have hadm : hax64ScalarAdmit f [.int a, .int b] (.int (fieldVal m p a b)) = true := by
    unfold hax64ScalarAdmit
    rw [hres, hsh, hto]
    simp only [Bool.true_and, Bool.and_true, scalarValNB]
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact ⟨h5, by omega, by omega⟩
  unfold hax64Exit
  rw [hbi]
  dsimp only
  rw [ite_eq_left (by simp [Value.isControlFlow, hadm])]

/-- **The run hypothesis from the field signature.** Let the module `m` have no callee and no
    linked function, let every head of `heads` answer canonical representatives with a
    canonical representative, and let the checker at `fieldKindSig p heads` accept the body
    the front reads in the context `entryKindsB σ` with the fuel bound `B`. Then the body runs
    to a value from the entry environment of every valuation that `σ` reads off an entry
    state satisfying `σ.Regions`, at every fuel `F ≥ B`. -/
theorem run_val_of_fieldCheck {m : HaxModule} {σ : AbiLayout} {p : ℕ} {heads : List String}
    (hheads : ∀ f ∈ heads, ∀ a b : ℕ, a < p → b < p →
      ∃ c : ℕ, hax64WExit f [.int a, .int b] = some (.int c) ∧ c < p)
    (hfns : m.fns = []) (hlk : m.linked = []) {ko : Option WKind} {B : Nat}
    (hc : (fieldKindSig p heads).check (entryKindsB σ) (nfBody (bindConsts σ.consts m.entry)) =
      some (ko, B))
    (fuelC : Nat) {F : Nat} (hF : B ≤ F) {sa : AState} (hR : σ.Regions sa)
    (V : Ctxt.Valuation (entryCtx (abiEntry σ))) (hV : AbiValOf σ sa (ctMapValD (mapVal V))) :
    ∃ v env', (denote' (crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC m.depth) F
      (nfBody (bindConsts σ.consts m.entry))).run (entryEnvOf (abiEntry σ) V) =
        (.val v, env') := by
  rw [crateBi_prepared_of_fns_nil hfns, HaxModule.linkTable_of_linked_nil hlk]
  exact KindSig.denote'_run_val_of_check (fieldKindSig_sound hheads) hc hF
    (envOK_entryEnvOf_of_abiValOf hR V hV)

/-- **Constant time of `compileA` on straight-line field code.** `haxc_ct_proved_all` (through
    `haxc_ct_proved_all_of_check`) at a module without callees and linked functions, with the
    precondition `True` and the run hypothesis from the checker at `fieldKindSig p heads`:
    every decoding of the bytes is constant time under `ctRegime` between entry states that
    satisfy `σ.Regions` and agree on the public data of `σ`, from the first of which `m` has a
    source run. -/
theorem ct_of_fieldCheck (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hfns : m.fns = []) (hlk : m.linked = []) {p : ℕ} {heads : List String}
    (hheads : ∀ f ∈ heads, ∀ a b : ℕ, a < p → b < p →
      ∃ c : ℕ, hax64WExit f [.int a, .int b] = some (.int c) ∧ c < p)
    {ko : Option WKind} {B : Nat}
    (hcheck : (fieldKindSig p heads).check (entryKindsB (pairStage m σ).2)
      (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry)) = some (ko, B))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup) {prog : List RInstr}
    (hd : decodeLprog bytes = some prog) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂ ∧ ∃ v, haxRuns σ m s₁ v)
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') :=
  fun s₁ s₂ t₁ t₂ h h₁ h₂ =>
  haxc_ct_proved_all_of_check s m σ fname P bytes hc B 0 (fun _ => True) hck
    (fun _ V hR _ hV => run_val_of_fieldCheck hheads ((pairStage_fns m σ).trans hfns)
      ((pairStage_linked m σ).trans hlk) hcheck 0 le_rfl hR V hV)
    hL hnds hd (by simp [hlk]) (by simp [hlk]) s₁ s₂ t₁ t₂
    ⟨h.1, h.2.1, h.2.2.1, trivial, trivial, h.2.2.2, .inl hlk⟩ h₁ h₂

/-! ## Loops carrying a field value -/

/-- **A carried field value keeps its range.** In a context binding `x` and `a` to the range
    `[0, p - 1]`, the checker at `fieldKindSig p heads` accepts the counted loop that binds
    `y` to `x` and rebinds it, `n` times, to the head `f ∈ heads` at `y` and `a`: the rebinding
    has the range `[0, p - 1]` of `y`, as the loop rule requires, and the loop returns `y` at
    that range with the fuel bound `n`. -/
theorem fieldKindSig_check_carried {p : ℕ} {heads : List String} {f : String} (hf : f ∈ heads)
    (n : Nat) :
    (fieldKindSig p heads).check [("a", .rng 0 ((p : Int) - 1)), ("x", .rng 0 ((p : Int) - 1))]
      (.letBind "y" (.var "x")
        (.seq (.forFold "_i" (.lit (.int 0)) (.lit (.int n))
          (.letBind "y" (.app f [.var "y", .var "a"]) (.var "y")))
          (.var "y"))) =
      some (some (.rng 0 ((p : Int) - 1)), n) := by
  simp (config := { decide := true }) [KindSig.check, KindSig.checkArgs, KindSig.ctxOK,
    List.lookup, fieldKindSig, wKindSig, hf]

/-! ## Signatures extended by further heads -/

/-- The signature `S` extended by the heads of `g`: a head that `S` does not type on its
    argument kinds is typed by `g`. -/
def kindSigOr {K : Type} (S : KindSig K) (g : String → List K → Option K) : KindSig K :=
  { S with sig := fun f ks => (S.sig f ks).orElse fun _ => g f ks }

/-- **Soundness of an extended signature.** If `S` is sound and every head `g` types answers
    arguments of its argument kinds with a value of its result kind, the extension is
    sound. -/
theorem kindSigOr_sound {K : Type} {S : KindSig K} {g : String → List K → Option K}
    {ofKind : K → Value → Prop} {bi : _root_.Hax.Builtins} (hS : S.Sound ofKind bi)
    (hg : ∀ f ks k, g f ks = some k → ∀ vs, KindSig.KindsOK ofKind ks vs →
      ∃ v, bi f vs = some v ∧ ofKind k v) :
    (kindSigOr S g).Sound ofKind bi where
  noCF := hS.noCF
  lit := hS.lit
  range := hS.range
  ctr := hS.ctr
  sig f ks k h vs hvs := by
    simp only [kindSigOr] at h
    cases hs : S.sig f ks with
    | none =>
      rw [hs] at h
      exact hg f ks k h vs hvs
    | some k' =>
      rw [hs] at h
      simp only [Option.orElse, Option.some.injEq] at h
      subst h
      exact hS.sig f ks _ hs vs hvs

/-- The checked `usize` product `Mul#size` on two ranges of words whose product is a word. -/
def mulSizeW : String → List WKind → Option WKind
  | "Mul#size", [.rng a b, .rng c d] =>
    if 0 ≤ a ∧ 0 ≤ c ∧ b < 2 ^ 64 ∧ d < 2 ^ 64 ∧ b * d < 2 ^ 64 then
      some (.rng (a * c) (b * d)) else none
  | _, _ => none

/-- `Mul#size` multiplies two words whose product is a word under `hax64WExit`. -/
theorem hax64WExit_mulSize {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hab : a * b < 2 ^ 64) :
    hax64WExit "Mul#size" [.int a, .int b] = some (.int ((a * b : Nat) : Int)) := by
  refine hax64WExit_word (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_ ?_ ha hb hab ?_
  · simp [exitScalarRes, CatCrypt.Crypto.Hax.exitScalarCall]
  · change exitMarshalOk (CatCrypt.Crypto.Hax.towerOfCallName_default "Mul#size") = true
    simp [CatCrypt.Crypto.Hax.towerOfCallName_default, CatCrypt.Crypto.Hax.arrCtorLen,
      exitMarshalOk, Jasmin.LowCT.TowerType.storageBytes]
  · unfold _root_.Hax.hax64Builtins
    rw [_root_.Hax.hax64WordOps_mulSize]
    unfold _root_.Hax.uintMulOp
    rw [ite_eq_left ⟨by omega, by omega, by omega, by omega, by exact_mod_cast hab⟩]
    simp

/-- **`Mul#size` is sound for `hax64WExit`**: on two words in the ranges of its argument
    kinds it answers a value in the product range. -/
theorem mulSizeW_sound : ∀ f ks k, mulSizeW f ks = some k → ∀ vs,
    KindSig.KindsOK wOfKind ks vs → ∃ v, hax64WExit f vs = some v ∧ wOfKind k v := by
  intro f ks k h vs hvs
  unfold mulSizeW at h
  split at h
  · next a b c d =>
    split_ifs at h with hc
    cases h
    rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
      simp only [KindSig.KindsOK, and_false] at hvs
    obtain ⟨⟨x, rfl, hx1, hx2⟩, ⟨y, rfl, hy1, hy2⟩, -⟩ := hvs
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ x)
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ y)
    have hxy : (n : Int) * m ≤ b * d := Int.mul_le_mul hx2 hy2 (by omega) (by omega)
    have hac : a * c ≤ (n : Int) * m := Int.mul_le_mul hx1 hy1 (by omega) (by omega)
    have hnm : n * m < 2 ^ 64 := by exact_mod_cast (by omega : (n : Int) * m < 2 ^ 64)
    refine ⟨_, hax64WExit_mulSize (by omega) (by omega) hnm, _, rfl, ?_, ?_⟩ <;> push_cast <;>
      omega
  · cases h

/-- The word signature of field code at the modulus `p`: the heads `heads` of
    `fieldKindSig p heads`, then `Mul#size`, then the word operations of `wKindSig`. -/
def fieldWordSig (p : ℕ) (heads : List String) : KindSig WKind :=
  kindSigOr (kindSigOr (fieldKindSig p heads) mulSizeW) wKindSig.sig

/-- **Soundness of the word signature of field code**, from the canonical answers of the
    heads. -/
theorem fieldWordSig_sound {p : ℕ} {heads : List String}
    (hheads : ∀ f ∈ heads, ∀ a b : ℕ, a < p → b < p →
      ∃ c : ℕ, hax64WExit f [.int a, .int b] = some (.int c) ∧ c < p) :
    (fieldWordSig p heads).Sound wOfKind hax64WExit :=
  kindSigOr_sound (kindSigOr_sound (fieldKindSig_sound hheads) mulSizeW_sound)
    wKindSig_sound.sig

/-! ## Arrays of canonical words -/

/-- The kinds of field code with array inputs: a word kind of `wKindSig`, or an array of `n`
    canonical words. -/
inductive CKind where
  | w (k : WKind)
  | carr (n : Nat)
  deriving DecidableEq, Repr

/-- The word kinds of a list of kinds, when every kind is a word kind. -/
def CKind.toWs : List CKind → Option (List WKind)
  | [] => some []
  | .w k :: ks => (CKind.toWs ks).map (k :: ·)
  | .carr _ :: _ => none

/-- The values of a kind at the modulus `p`: a word kind holds the values of `wOfKind`, and an
    array of `n` canonical words is the array of the integers of `n` numbers below `p`. -/
def cOfKind (p : ℕ) : CKind → Value → Prop
  | .w k, v => wOfKind k v
  | .carr n, v => ∃ xs : List Nat, v = .array (xs.map fun x : Nat => Value.int (x : Int)) ∧
      xs.length = n ∧ ∀ x ∈ xs, x < p

/-- Values of a list of word kinds lifted to `CKind` have the word kinds. -/
theorem kindsOK_of_toWs {p : ℕ} : ∀ {ks : List CKind} {ks' : List WKind} {vs : List Value},
    CKind.toWs ks = some ks' → KindSig.KindsOK (cOfKind p) ks vs →
      KindSig.KindsOK wOfKind ks' vs
  | [], _, [], h, _ => by cases h; trivial
  | [], _, _ :: _, _, hv => hv.elim
  | .w _ :: _, _, [], _, hv => hv.elim
  | .w k :: ks, ks', v :: vs, h, hv => by
    simp only [CKind.toWs, Option.map_eq_some_iff] at h
    obtain ⟨ks'', h', rfl⟩ := h
    exact ⟨hv.1, kindsOK_of_toWs h' hv.2⟩
  | .carr _ :: _, _, _, h, _ => by cases h

/-- The kind signature of field code with arrays of canonical words at the modulus `p`
    over the word signature `S`: `index` reads a canonical word from an array of `n`
    canonical words at an index range inside `[0, n - 1]`, `array_update` writes a canonical
    word into it, and every other head on word kinds is typed by `S`. -/
def canonKindSig (p : ℕ) (S : KindSig WKind) : KindSig CKind where
  lit l := (S.lit l).map .w
  sig f ks :=
    match f, ks with
    | "index", [.carr n, .w (.rng a b)] =>
      if 0 ≤ a ∧ b < n then some (.w (.rng 0 ((p : Int) - 1))) else none
    | "array_update", [.carr n, .w (.rng a b), .w (.rng c d)] =>
      if 0 ≤ a ∧ b < n ∧ 0 ≤ c ∧ d < p then some (.carr n) else none
    | f, ks => (CKind.toWs ks).bind fun ks' => (S.sig f ks').map .w
  range
    | .w k => S.range k
    | .carr _ => none
  ctr a c := .w (S.ctr a c)

/-- **Soundness of the signature of canonical arrays.** If the word signature `S` is sound
    for `wOfKind` and `hax64WExit`, so is `canonKindSig p S` for `cOfKind p`. -/
theorem canonKindSig_sound {p : ℕ} {S : KindSig WKind} (hS : S.Sound wOfKind hax64WExit) :
    (canonKindSig p S).Sound (cOfKind p) hax64WExit where
  noCF k v h := by
    cases k with
    | w k => exact hS.noCF k v h
    | carr n =>
      obtain ⟨_, rfl, _⟩ := h
      rfl
  lit l k h := by
    simp only [canonKindSig, Option.map_eq_some_iff] at h
    obtain ⟨k', hk, rfl⟩ := h
    exact hS.lit l k' hk
  sig f ks k h vs hvs := by
    simp only [canonKindSig] at h
    split at h
    · next n a b =>
      split_ifs at h with hc
      cases h
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
        simp only [KindSig.KindsOK, and_false] at hvs
      obtain ⟨⟨xs, rfl, hlen, hxs⟩, ⟨i, rfl, hi1, hi2⟩, -⟩ := hvs
      obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
      have hj : j < (xs.map fun x : Nat => Value.int (x : Int)).length := by simp; omega
      have hx := hxs _ (List.getElem_mem (by simpa using hj : j < xs.length))
      refine ⟨_, CatCrypt.Crypto.Hax.arrayOps_hax64WExit.index _ j hj
        (by simp [Value.isControlFlow]), ?_⟩
      simp only [List.getElem_map]
      exact ⟨_, rfl, by omega, by omega⟩
    · next n a b c d =>
      split_ifs at h with hc
      cases h
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩ <;>
        simp only [KindSig.KindsOK, and_false] at hvs
      obtain ⟨⟨xs, rfl, hlen, hxs⟩, ⟨i, rfl, hi1, hi2⟩, ⟨u, rfl, hu1, hu2⟩, -⟩ := hvs
      obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
      obtain ⟨t, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ u)
      have hj : j < (xs.map fun x : Nat => Value.int (x : Int)).length := by simp; omega
      refine ⟨_, CatCrypt.Crypto.Hax.arrayOps_hax64WExit.update _ j _ hj, xs.set j t, ?_,
        by simpa using hlen, ?_⟩
      · rw [List.map_set]
      · intro x hx
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact hxs x hx
        · omega
    · obtain ⟨ks', hks, hk⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
      exact hS.sig f ks' k' hk' vs (kindsOK_of_toWs hks hvs)
  range k a b h v hv := by
    cases k with
    | w k => exact hS.range k a b h v hv
    | carr n => cases h
  ctr a c n h1 h2 := hS.ctr a c n h1 h2

/-! ## Canonical entries -/

/-- The kind of a parameter under canonical entries at the modulus `p`: an array parameter
    of `n` words is an array of `n` canonical words, and a scalar parameter is in the range
    `[0, p - 1]`. -/
def argKindC (p : ℕ) (a : AbiArg) : CKind :=
  match a.kind with
  | .words n => .carr n
  | .scalar => .w (.rng 0 ((p : Int) - 1))

/-- The kinds of the parameters of the entry of the layout `σ` under canonical entries at the
    modulus `p`, in the order of the entry. -/
def entryKindsC (σ : AbiLayout) (p : ℕ) : List (String × CKind) :=
  σ.args.reverse.map fun a => (a.name, argKindC p a)

/-- **Canonical entries.** The precondition on entry states at the modulus `p`: every word
    `σ` reads off the state, a scalar parameter's register or a word of an array parameter at
    its register's address, is below `p`. -/
def canonPre (σ : AbiLayout) (p : ℕ) (sa : AState) : Prop :=
  ∀ a ∈ σ.args, match a.kind with
    | .scalar => (sa.regs a.reg).toNat < p
    | .words n => ∀ k : Fin n, (wordsFn sa (sa.regs a.reg) n k).toNat < p

/-- **The entry environment binds the parameters at their canonical kinds.** Let every word
    the parameters `as` read off the state `sa` be below `p`, and let every register variable
    and every array variable of the mapped context of `as` read, in the mapped valuation of
    `V`, the register of its parameter or the words at that register's address. Then the entry
    environment of `V` binds each parameter to a value of its kind `argKindC p`. -/
theorem envOK_entryEnvOf_canon (sa : AState) {p : ℕ} : ∀ (as : List AbiArg)
    (V : Ctxt.Valuation (entryCtx (as.map fun a => (a.name, abiKindArr a.kind)))),
    (∀ a ∈ as, match a.kind with
      | .scalar => (sa.regs a.reg).toNat < p
      | .words n => ∀ k : Fin n, (wordsFn sa (sa.regs a.reg) n k).toNat < p) →
    (∀ {w : Nat} (v : Ctxt.Var (d := jasminDialect)
        (mapCtx ((entryCtx (as.map fun a => (a.name, abiKindArr a.kind))).map catTy)) (.reg w)),
      ∃ a, as[varIndex v]? = some a ∧
        ∃ h : w = 64, v.lookup (ctMapValD (mapVal V)) = h ▸ sa.regs a.reg) →
    (∀ {w n : Nat} (v : Ctxt.Var (d := jasminDialect)
        (mapCtx ((entryCtx (as.map fun a => (a.name, abiKindArr a.kind))).map catTy))
        (.stackArr w n)),
      ∃ a, as[varIndex v]? = some a ∧
        ∃ h : w = 64, v.lookup (ctMapValD (mapVal V)) = h ▸ wordsFn sa (sa.regs a.reg) n) →
    KindSig.EnvOK (cOfKind p) (as.map fun a => (a.name, argKindC p a))
      (entryEnvOf (as.map fun a => (a.name, abiKindArr a.kind)) V)
  | [], _, _, _, _ => fun _ _ h => by simp at h
  | ⟨name, reg, kind⟩ :: as, .cons y V, hc, hr, harr => by
      have ih := envOK_entryEnvOf_canon sa as V
        (fun a ha => hc a (List.mem_cons_of_mem _ ha))
        (fun v => by
          obtain ⟨a, ha, hw, hl⟩ := hr v.there
          exact ⟨a, ha, hw, hl⟩)
        (fun v => by
          obtain ⟨a, ha, hw, hl⟩ := harr v.there
          exact ⟨a, ha, hw, hl⟩)
      refine KindSig.envOK_extend ih ?_
      have hca := hc _ List.mem_cons_self
      cases kind with
      | words n =>
        obtain ⟨a, ha, hw, hy⟩ := harr (w := 64) (n := n) .here
        cases hw
        cases ha
        change (fun k => BitVec.ofNat 64 (y k).toNat) = wordsFn sa (sa.regs reg) n at hy
        change ∀ k : Fin n, (wordsFn sa (sa.regs reg) n k).toNat < p at hca
        refine ⟨List.ofFn fun i => (y i).toNat, ?_, by simp, ?_⟩
        · simp [List.map_ofFn, Function.comp_def]
          rfl
        · intro x hx
          obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
          have := hca k
          rw [← hy] at this
          simpa using this
      | scalar =>
        obtain ⟨a, ha, hw, hy⟩ := hr (w := 64) .here
        cases hw
        cases ha
        change y = sa.regs reg at hy
        change (sa.regs reg).toNat < p at hca
        subst hy
        exact ⟨_, rfl, by omega, by omega⟩

/-- **The entry environment of a canonical entry state binds the parameters at their
    canonical kinds.** For an entry state `sa` satisfying `canonPre σ p` and a valuation `V`
    whose mapped valuation `σ` reads off `sa`, the entry environment of `V` binds each
    parameter to a value of its kind in `entryKindsC σ p`. -/
theorem envOK_entryEnvOf_of_canonPre {σ : AbiLayout} {p : ℕ} {sa : AState}
    (hP : canonPre σ p sa) (V : Ctxt.Valuation (entryCtx (abiEntry σ)))
    (hV : AbiValOf σ sa (ctMapValD (mapVal V))) :
    KindSig.EnvOK (cOfKind p) (entryKindsC σ p) (entryEnvOf (abiEntry σ) V) := by
  have hrev : abiEntry σ = σ.args.reverse.map fun a => (a.name, abiKindArr a.kind) := by
    simp [abiEntry, abiParamsArr, List.map_reverse]
  unfold entryKindsC
  revert V
  rw [hrev]
  intro V hV
  have hlt : ∀ {t : JasminDialect.JasminTy} (v : Ctxt.Var (d := jasminDialect)
      (mapCtx ((entryCtx (σ.args.reverse.map fun a => (a.name, abiKindArr a.kind))).map
        catTy)) t),
      ∀ a, σ.args[X86Backend.ExportCertEntry.argIdx v]? = some a →
        σ.args.reverse[varIndex v]? = some a := by
    intro t v a ha
    have hlt := JasminLsemSimulation.varIndex_lt v
    simp only [mapCtx, entryCtx, List.length_map, List.length_reverse] at hlt
    simp only [X86Backend.ExportCertEntry.argIdx, mapCtx, entryCtx, List.length_map,
      List.length_reverse] at ha
    exact (List.getElem?_reverse hlt).trans ha
  refine envOK_entryEnvOf_canon sa σ.args.reverse V
    (fun a ha => hP a (List.mem_reverse.mp ha)) (fun {w} v => ?_) (fun {w n} v => ?_)
  · obtain ⟨a, ha, -, hw, hl⟩ := hV.reg v
    exact ⟨a, hlt v a ha, hw, hl⟩
  · obtain ⟨a, ha, -, hw, hl⟩ := hV.arr v
    exact ⟨a, hlt v a ha, hw, hl⟩

/-- **The run hypothesis from the checker under canonical entries.** Let the module `m` have
    no callee and no linked function, let the word signature `S` be sound, and let the
    checker at `canonKindSig p S` accept the body the front reads in the context
    `entryKindsC σ p` with the fuel bound `B`. Then the body runs to a value from the entry
    environment of every valuation that `σ` reads off an entry state satisfying
    `canonPre σ p`, at every callee fuel and every fuel `F ≥ B`. -/
theorem run_val_of_canonCheck {m : HaxModule} {σ : AbiLayout} {p : ℕ} {S : KindSig WKind}
    (hS : S.Sound wOfKind hax64WExit) (hfns : m.fns = []) (hlk : m.linked = [])
    {ko : Option CKind} {B : Nat}
    (hc : (canonKindSig p S).check (entryKindsC σ p) (nfBody (bindConsts σ.consts m.entry)) =
      some (ko, B))
    (fuelC : Nat) {F : Nat} (hF : B ≤ F) {sa : AState} (hP : canonPre σ p sa)
    (V : Ctxt.Valuation (entryCtx (abiEntry σ))) (hV : AbiValOf σ sa (ctMapValD (mapVal V))) :
    ∃ v env', (denote' (crateBi (m.prepared nfBody) (m.linkTable hax64WExit) fuelC m.depth) F
      (nfBody (bindConsts σ.consts m.entry))).run (entryEnvOf (abiEntry σ) V) =
        (.val v, env') := by
  rw [crateBi_prepared_of_fns_nil hfns, HaxModule.linkTable_of_linked_nil hlk]
  exact KindSig.denote'_run_val_of_check (canonKindSig_sound hS) hc hF
    (envOK_entryEnvOf_of_canonPre hP V hV)

/-- **Constant time of `compileA` on field code with canonical entries.**
    `haxc_ct_proved_all` (through `haxc_ct_proved_all_of_check`) at a module without callees
    and linked functions, with the precondition `canonPre` of the layout of the pair stage at
    the modulus `p` and the run hypothesis from the checker at `canonKindSig p S` for a sound
    word signature `S`: every decoding of the bytes is constant time under `ctRegime` between
    entry states that satisfy `σ.Regions` and `canonPre`, agree on the public data of `σ`, and
    from the first of which `m` has a source run. -/
theorem ct_of_fieldCheckPre (s : _root_.Hax.FnSecrecy) (m : HaxModule) (σ : AbiLayout)
    (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes))
    (hck : haxToNFCTBL s (pairStage m σ).2 (pairStage m σ).1 = true)
    (hfns : m.fns = []) (hlk : m.linked = []) {p : ℕ} {S : KindSig WKind}
    (hS : S.Sound wOfKind hax64WExit) {ko : Option CKind} {B : Nat}
    (hcheck : (canonKindSig p S).check (entryKindsC (pairStage m σ).2 p)
      (nfBody (bindConsts (pairStage m σ).2.consts (pairStage m σ).1.entry)) = some (ko, B))
    (hL : PubLabelsOK (pairStage m σ).2 (mapLabels (nfLabels s (abiEntry (pairStage m σ).2))))
    (hnds : (pairStage m σ).2.envNames.Nodup) {prog : List RInstr}
    (hd : decodeLprog bytes = some prog) :
    ConstantTimeRel
      (fun s₁ s₂ => σ.PubAgree s₁ s₂ ∧ σ.Regions s₁ ∧ σ.Regions s₂
        ∧ canonPre (pairStage m σ).2 p s₁ ∧ canonPre (pairStage m σ).2 p s₂
        ∧ ∃ v, haxRuns σ m s₁ v)
      (fun s t => ∃ s', RunL ctRegime (fun _ _ => True) prog 0 s t s') :=
  fun s₁ s₂ t₁ t₂ h h₁ h₂ =>
  haxc_ct_proved_all_of_check s m σ fname P bytes hc B 0 (canonPre (pairStage m σ).2 p) hck
    (fun _ V _ hP hV => run_val_of_canonCheck hS ((pairStage_fns m σ).trans hfns)
      ((pairStage_linked m σ).trans hlk) hcheck 0 le_rfl hP V hV)
    hL hnds hd (by simp [hlk]) (by simp [hlk]) s₁ s₂ t₁ t₂
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, .inl hlk⟩ h₁ h₂

end CatCrypt.Crypto.SecureCompilation.Haxc
