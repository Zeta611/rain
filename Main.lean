inductive 𝔼ₜ
  | add (n : Nat)
  | mul (n : Nat)

declare_syntax_cat exp_t
syntax ("ADD " <|> "MUL ") term : exp_t
syntax "T⟪ " exp_t " ⟫" : term
macro_rules
  | `(T⟪ ADD $n ⟫) => `(𝔼ₜ.add $n)
  | `(T⟪ MUL $n ⟫) => `(𝔼ₜ.mul $n)

/- Metaprogramming from the object language T's perspective -/
#eval T⟪ ADD (42 + 5) ⟫

inductive 𝕍ₜ
  | nat (n : Nat)

instance : OfNat 𝕍ₜ n where
  ofNat := .nat n

instance : Coe Nat 𝕍ₜ where
  coe := .nat

instance : Coe 𝕍ₜ Nat where
  coe := λ (.nat n) => n

#eval (42 : 𝕍ₜ)

def semₜ : 𝔼ₜ → 𝕍ₜ → 𝕍ₜ
  | .add n, .nat m => n + m
  | .mul n, .nat m => n * m

macro "⟦ " e:exp_t " ⟧" : term => `(semₜ T⟪ $e ⟫)
macro "⟦ " e:term " ⟧" : term => `(semₜ $e)

#eval ⟦ ADD 42 ⟧ 10
#eval ⟦ T⟪ ADD 42 ⟫ ⟧ 10
#eval ⟦ MUL 42 ⟧ 3

inductive 𝔼ₛ
  | var
  | nat (n : Nat)
  | add (e₁ e₂ : 𝔼ₛ)
  | mul (e₁ e₂ : 𝔼ₛ)
  | equal (e₁ e₂ : 𝔼ₛ)
  | pair (e₁ e₂ : 𝔼ₛ)
  | proj₁ (e : 𝔼ₛ)
  | proj₂ (e : 𝔼ₛ)
  | ite (eᵢ eₜ eₑ : 𝔼ₛ)

instance : OfNat 𝔼ₛ n where
  ofNat := .nat n

instance : Coe Nat 𝔼ₛ where
  coe := .nat

declare_syntax_cat exp_s
syntax num : exp_s
syntax ident : exp_s
syntax:40 exp_s:40 " = " exp_s:41 : exp_s
syntax:50 exp_s:50 " + " exp_s:51 : exp_s
syntax:60 exp_s:60 " * " exp_s:61 : exp_s
syntax "( " exp_s ", " exp_s " )" : exp_s
syntax "( " exp_s " )" : exp_s
syntax exp_s (".1" <|> ".2") : exp_s
syntax "if " "( " exp_s " ) " "then" " { " exp_s " } " "else" " { " exp_s " }" : exp_s
syntax "S⟪ " exp_s " ⟫" : term
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

#eval S⟪
  if (x.1.1 = 0) then {
    x.1.2 + x.2
  } else {
    x.1.2 * x.2
  }
⟫
#eval S⟪ x ⟫

inductive 𝕍ₛ
  | nat (n : Nat)
  | pair (v₁ v₂ : 𝕍ₛ)

instance : OfNat 𝕍ₛ n where
  ofNat := .nat n

instance : Coe Nat 𝕍ₛ where
  coe := .nat

instance : Coe 𝕍ₛ 𝕍ₛ where
  coe n := n

instance [Coe A 𝕍ₛ] [Coe B 𝕍ₛ] : Coe (A × B) 𝕍ₛ where
  coe := λ (a, b) => .pair (Coe.coe a) (Coe.coe b)

#eval (((1, 2), 3) : 𝕍ₛ)

def encodeEₜₛ : 𝔼ₜ → 𝕍ₛ
  | T⟪ ADD n ⟫ => (0, n)
  | T⟪ MUL n ⟫ => (1, n)

macro "⌈ " e:exp_t " ⌉" : term => `(encodeEₜₛ T⟪ $e ⟫)
macro "⌈ " e:term " ⌉" : term => `(encodeEₜₛ $e)

#eval ⌈ T⟪ ADD 42 ⟫ ⌉
#eval ⌈ MUL 42 ⌉

def encodeVₜₛ : 𝕍ₜ → 𝕍ₛ
  | .nat n => n

macro "⌈ " e:term " ⌉" : term => `(encodeVₜₛ $e)

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
  | .pair e₁ e₂, v => do
    let v1 ← semₛ e₁ v
    let v2 ← semₛ e₂ v
    (v1, v2)
  | .proj₁ e, v => do
    let v' ← semₛ e v
    match v' with
      | .pair v1 _ => v1
      | _ => none
  | .proj₂ e, v => do
    let v' ← semₛ e v
    match v' with
      | .pair _ v2 => v2
      | _ => none
  | .ite eᵢ eₜ eₑ, v => do
    let p ← semₛ eᵢ v
    match p with
      | 0 => semₛ eₑ v
      | _ => semₛ eₜ v

macro "⟦ " e:exp_s " ⟧" : term => `(semₛ S⟪ $e ⟫)
macro "⟦ " e:term " ⟧" : term => `(semₛ $e)

def Iₛₜ : 𝔼ₛ := S⟪
  if (x.1.1 = 0) then {
    x.1.2 + x.2
  } else {
    x.1.2 * x.2
  }
⟫

#eval if let some v := ⟦ Iₛₜ ⟧ (⌈ T⟪ ADD 3 ⟫ ⌉, ⌈ 4 ⌉)
  then v else 99

#eval if let some v := ⟦ Iₛₜ ⟧ (⌈ T⟪ MUL 3 ⟫ ⌉, ⌈ 4 ⌉)
  then v else 99
