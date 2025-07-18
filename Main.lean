inductive 𝔼ₜ where
  | add (n : Nat) : 𝔼ₜ
  | mul (n : Nat) : 𝔼ₜ

declare_syntax_cat exp_t
syntax "ADD" term : exp_t
syntax "MUL" term : exp_t
syntax "T⟪" exp_t "⟫" : term
macro_rules
  | `(T⟪ ADD $n ⟫) => `(𝔼ₜ.add $n)
  | `(T⟪ MUL $n ⟫) => `(𝔼ₜ.mul $n)

#eval T⟪ ADD 0 ⟫
#eval T⟪ MUL 0 ⟫

inductive 𝕍ₜ where
  | nat (n : Nat) : 𝕍ₜ

instance : OfNat 𝕍ₜ n where
  ofNat := .nat n

instance : Coe Nat 𝕍ₜ where
  coe := .nat

instance : Coe 𝕍ₜ Nat where
  coe := λ (.nat n) => n

#eval (42 : 𝕍ₜ)

def semₜ : 𝔼ₜ → 𝕍ₜ → 𝕍ₜ
  | T⟪ ADD n ⟫, (m : Nat) => n + m
  | T⟪ MUL n ⟫, (m : Nat) => n * m

macro "⟦" e:exp_t "⟧" : term => do
  `(semₜ T⟪ $e ⟫)

#eval ⟦ ADD 42 ⟧ 10
#eval ⟦ MUL 42 ⟧ 3

inductive 𝔼ₛ where
  | var : 𝔼ₛ
  | nat (n : Nat) : 𝔼ₛ
  | add (e₁ e₂ : 𝔼ₛ) : 𝔼ₛ
  | mul (e₁ e₂ : 𝔼ₛ) : 𝔼ₛ
  | equal (e₁ e₂ : 𝔼ₛ) : 𝔼ₛ
  | pair (e₁ e₂ : 𝔼ₛ) : 𝔼ₛ
  | proj₁ (e : 𝔼ₛ) : 𝔼ₛ
  | proj₂ (e : 𝔼ₛ) : 𝔼ₛ
  | ite (eᵢ eₜ eₑ : 𝔼ₛ) : 𝔼ₛ

declare_syntax_cat exp_s
syntax num : exp_s
syntax "x" : exp_s
syntax:40 exp_s:40 "=" exp_s:41 : exp_s
syntax:50 exp_s:50 "+" exp_s:51 : exp_s
syntax:60 exp_s:60 "*" exp_s:61 : exp_s
syntax "(" exp_s "," exp_s ")" : exp_s
syntax "(" exp_s ")" : exp_s
syntax exp_s ".1" : exp_s
syntax exp_s ".2" : exp_s
syntax "if" "(" exp_s ")" "then" "{" exp_s "}" "else" "{" exp_s "}" : exp_s
syntax "S⟪" exp_s "⟫" : term
macro_rules
  | `(S⟪ x ⟫) => `(𝔼ₛ.var)
  | `(S⟪ $n:num ⟫) => `(𝔼ₛ.nat $n)
  | `(S⟪ $e₁:exp_s + $e₂:exp_s ⟫) => `(𝔼ₛ.add S⟪ $e₁ ⟫ S⟪ $e₂ ⟫)
  | `(S⟪ $e₁:exp_s * $e₂:exp_s ⟫) => `(𝔼ₛ.mul S⟪ $e₁ ⟫ S⟪ $e₂ ⟫)
  | `(S⟪ $e₁:exp_s = $e₂:exp_s ⟫) => `(𝔼ₛ.equal S⟪ $e₁ ⟫ S⟪ $e₂ ⟫)
  | `(S⟪ ($e₁:exp_s, $e₂:exp_s) ⟫) => `(𝔼ₛ.pair S⟪ $e₁ ⟫ S⟪ $e₂ ⟫)
  | `(S⟪ ($e:exp_s) ⟫) => `(𝔼ₛ.pair S⟪ $e ⟫ S⟪ $e ⟫)
  | `(S⟪ $e:exp_s.1 ⟫) => `(𝔼ₛ.proj₁ S⟪ $e ⟫)
  | `(S⟪ $e:exp_s.2 ⟫) => `(𝔼ₛ.proj₂ S⟪ $e ⟫)
  | `(S⟪ if ($eᵢ:exp_s) then { $eₜ:exp_s } else { $eₑ:exp_s } ⟫) =>
      `(𝔼ₛ.ite S⟪ $eᵢ ⟫ S⟪ $eₜ ⟫ S⟪ $eₑ ⟫)

#eval S⟪ if (x.1.1 = 0) then { x.1.2 + x.2 } else { x.1.2 * x.2 } ⟫
#eval S⟪ 3 ⟫

inductive 𝕍ₛ where
  | nat (n : Nat) : 𝕍ₛ
  | pair (v₁ v₂ : 𝕍ₛ) : 𝕍ₛ

instance : OfNat 𝕍ₛ n where
  ofNat := .nat n

instance : CoeOut Nat 𝕍ₛ where
  coe := .nat

instance [CoeOut A 𝕍ₛ] [CoeOut B 𝕍ₛ] : CoeOut (A × B) 𝕍ₛ where
  coe := λ (a, b) => .pair (CoeOut.coe a) (CoeOut.coe b)


#eval (((1, 2), 3) : 𝕍ₛ)

def encodeEₜₛ : 𝔼ₜ → 𝕍ₛ
  | T⟪ ADD n ⟫ => (0, n)
  | T⟪ MUL n ⟫ => (1, n)

macro "⌈" e:exp_t "⌉" : term => do
  `(encodeEₜₛ T⟪ $e ⟫)

#eval ⌈ ADD 42 ⌉
#eval ⌈ MUL 42 ⌉

def encodeVₜₛ : 𝕍ₜ → 𝕍ₛ
  | .nat n => n

macro "⌈" e:term "⌉" : term => do
  `(encodeVₜₛ $e)

#eval ⌈ 42 ⌉

def semₛ : 𝔼ₛ → 𝕍ₛ → Option 𝕍ₛ
  | .var, v => v
  | .nat n, _ => n
  | .add e₁ e₂, v => do
    let v1 ← semₛ e₁ v
    let v2 ← semₛ e₂ v
    match (v1, v2) with
      | (.nat n1, .nat n2) => n1 + n2
      | _ => none
  | .mul e₁ e₂, v => do
    let v1 ← semₛ e₁ v
    let v2 ← semₛ e₂ v
    match (v1, v2) with
      | (.nat n1, .nat n2) => n1 * n2
      | _ => none
  | .equal e₁ e₂, v => do
    let v1 ← semₛ e₁ v
    let v2 ← semₛ e₂ v
    match (v1, v2) with
      | (.nat n1, .nat n2) => 𝕍ₛ.nat (if n1 = n2 then 1 else 0)
      | _ => none
  | 𝔼ₛ.pair e₁ e₂, v => do
    let v1 ← semₛ e₁ v
    let v2 ← semₛ e₂ v
    𝕍ₛ.pair v1 v2
  | 𝔼ₛ.proj₁ e, v => do
    let v' ← semₛ e v
    match v' with
      | .pair v1 _ => v1
      | _ => none
  | 𝔼ₛ.proj₂ e, v => do
    let v' ← semₛ e v
    match v' with
      | .pair _ v2 => v2
      | _ => none
  | 𝔼ₛ.ite eᵢ eₜ eₑ, v => do
    let p ← semₛ eᵢ v
    match p with
      | 0 => semₛ eₑ v
      | _ => semₛ eₜ v

macro "⟦" e:exp_s "⟧" : term => do
  `(semₛ S⟪ $e ⟫)

#eval if let some v := ⟦ 1 + 2 * 3 ⟧ 0 then v else 99

def Iₛₜ : 𝔼ₛ := S⟪ if (x.1.1 = 0) then { x.1.2 + x.2 } else { x.1.2 * x.2 } ⟫
#eval if let some v :=
  ⟦ if (x.1.1 = 0) then { x.1.2 + x.2 } else { x.1.2 * x.2 } ⟧ (.pair ⌈ MUL 3 ⌉ ⌈ 4 ⌉)
  then v else 99

#eval if let some v :=
  ⟦ if (x.1.1 = 0) then { x.1.2 + x.2 } else { x.1.2 * x.2 } ⟧ (.pair ⌈ ADD 3 ⌉ ⌈ 4 ⌉)
  then v else 99
