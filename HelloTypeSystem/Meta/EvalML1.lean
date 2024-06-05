import HelloTypeSystem.ML1

namespace HelloTypeSystem.ML1

notation:50 e:51 " ⇓ " n:51 => Judgement.Eval e n

/-!
# 整数・真偽値式の評価
-/

/-!
## 導出システムEvalML1(Err)の評価の例

### 練習問題3.1 \[基礎概念,§3.1]
-/

theorem «3 + 5 ⇓ 8» : Derivable (3 + 5 ⇓ 8) :=
  ⟨.E_Plus .E_Int .E_Int (.B_Plus rfl)⟩

theorem «8 - 2 - 3 ⇓ 3» : Derivable (8 - 2 - 3 ⇓ 3) :=
  ⟨.E_Minus
    (.E_Minus .E_Int .E_Int (.B_Minus rfl))
    .E_Int
    (.B_Minus rfl)
  ⟩

theorem «(4 + 5) * (1 - 10) ⇓ -81» : Derivable ((4 + 5) * (1 - 10) ⇓ (-81 : Int)) :=
  ⟨.E_Times
    (.E_Plus .E_Int .E_Int (.B_Plus rfl))
    (.E_Minus .E_Int .E_Int (.B_Minus rfl))
    (.B_Times rfl)
  ⟩

theorem «if 4 < 5 then 2 + 3 else 8 * 8 ⇓ 5» : Derivable (.If (.LT 4 5) (2 + 3) (8 * 8) ⇓ 5) :=
  ⟨.E_IfT
    (.E_LT .E_Int .E_Int (.B_LTT <| by simp))
    (.E_Plus .E_Int .E_Int (.B_Plus rfl))
  ⟩

theorem «3 + if -23 < -2 * 8 then 8 else 2 + 4 ⇓ 11» : Derivable (3 + (.If (.LT (-23 : Int) ((-2 : Int) * 8)) 8 (2 + 4)) ⇓ 11) :=
  ⟨.E_Plus
    .E_Int
    (.E_IfT
      (.E_LT
        .E_Int
        (.E_Times .E_Int .E_Int (.B_Times rfl))
        (.B_LTT <| by simp)
      )
      .E_Int
    )
    (.B_Plus rfl)
  ⟩

theorem «3 + (if -23 < -2 * 8 then 8 else 2) + 4 ⇓ 15» : Derivable (3 + (.If (.LT (-23 : Int) ((-2 : Int) * 8)) 8 2) + 4 ⇓ 15) :=
  ⟨.E_Plus
    (.E_Plus
      .E_Int
      (.E_IfT
        (.E_LT
          .E_Int
          (.E_Times .E_Int .E_Int (.B_Times rfl))
          (.B_LTT <| by simp)
        )
        .E_Int
      )
      (.B_Plus rfl)
    )
    .E_Int
    (.B_Plus rfl)
  ⟩

/-!
### 練習問題3.3 \[基礎概念,§3.2]
-/

theorem «1 + true ⇓ error_+» : Derivable (1 + true ⇓ Error.Plus) :=
  ⟨.E_PlusIntBool .E_Int .E_Bool⟩

theorem «1 + true + 2 ⇓ error_+» : Derivable (1 + true + 2 ⇓ Error.Plus) :=
  have ⟨𝒟⟩ := «1 + true ⇓ error_+»
  ⟨.E_PlusErr 𝒟⟩

theorem «if 2 + 3 then 1 else 3 ⇓ error_if_cond» : Derivable (.If (2 + 3) 1 3 ⇓ Error.IfCond) :=
  ⟨.E_IfCondInt (.E_Plus .E_Int .E_Int (.B_Plus rfl))⟩

theorem «if 3 < 4 then 1 < true else 3 - false ⇓ error_<» : Derivable (.If (.LT 3 4) (.LT 1 true) (3 - false) ⇓ Error.LT) :=
  ⟨.E_IfTErr
    (.E_LT .E_Int .E_Int (.B_LTT (by simp)))
    (.E_LTIntBool .E_Int .E_Bool)
  ⟩

/-!
## 導出システムEvalML1のメタ定理

### 評価の一意性：定理3.2 \[基礎概念,§3.1]
-/

/--
EvalML1の評価の一意性（定理3.2・練習問題3.2 \[基礎概念,§3.1]）

付帯条件の一意性はLeanのEqによって自然に示せる。
例えば加算について、
- 仮定から`h₁.symm : i₃ = i₁ + i₂`
- 仮定から`h₂ : i₁' + i₂' = i₃'`
- 左辺の導出について帰納法の仮定から`hl : i₁ = i₁'`
- 右辺の導出について帰納法の仮定から`hr : i₂ = i₂'`

より
```
i₃ = i₁  + i₂  -- h₁.symm
   = i₁' + i₂  -- hl
   = i₁' + i₂' -- hr
   = i₃'       -- h₂
```
したがって`h₂ ▸ hr ▸ hl ▸ h₁.symm : i₃ = i₃'`が証明になる。
-/
theorem eval_value_uniq {v₁ v₂ : Value} : {e : Expr} → Derivation (e ⇓ v₁) → Derivation (e ⇓ v₂) → v₁ = v₂
  | .C (.Z _), .E_Int,  .E_Int  => rfl
  | .C (.B _), .E_Bool, .E_Bool => rfl
  | .Add .., .E_Plus d₁l d₁r (.B_Plus h₁), .E_Plus d₂l d₂r (.B_Plus h₂) =>
      have hl := eval_value_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_value_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.Z (h₂ ▸ hr ▸ hl ▸ h₁.symm)
  | .Sub .., .E_Minus d₁l d₁r (.B_Minus h₁), .E_Minus d₂l d₂r (.B_Minus h₂) =>
      have hl := eval_value_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_value_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.Z (h₂ ▸ hr ▸ hl ▸ h₁.symm)
  | .Mul .., .E_Times d₁l d₁r (.B_Times h₁), .E_Times d₂l d₂r (.B_Times h₂) =>
      have hl := eval_value_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_value_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.Z (h₂ ▸ hr ▸ hl ▸ h₁.symm)
  | .LT .., .E_LT _ _ (.B_LTT _), .E_LT _ _ (.B_LTT _) => rfl
  | .LT .., .E_LT _ _ (.B_LTF _), .E_LT _ _ (.B_LTF _) => rfl
  | .LT .., .E_LT d₁l d₁r (.B_LTT h₁), .E_LT d₂l d₂r (.B_LTF h₂) =>
      have hl := eval_value_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_value_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.B <| False.elim <| absurd (hr ▸ hl ▸ h₁) h₂
  | .LT .., .E_LT d₁l d₁r (.B_LTF h₁), .E_LT d₂l d₂r (.B_LTT h₂) =>
      have hl := eval_value_uniq d₁l d₂l |> Value.Z.inj
      have hr := eval_value_uniq d₁r d₂r |> Value.Z.inj
      congrArg Value.B <| False.elim <| absurd (hr ▸ hl ▸ h₂) h₁
  | .If .., .E_IfT _ d₁v, .E_IfT _ d₂v =>
      eval_value_uniq d₁v d₂v
  | .If .., .E_IfF _ d₁v, .E_IfF _ d₂v =>
      eval_value_uniq d₁v d₂v
  | .If .., .E_IfT d₁c _, .E_IfF d₂c _ =>
      have := eval_value_uniq d₁c d₂c
      by contradiction
  | .If .., .E_IfF d₁c _, .E_IfT d₂c _ =>
      have := eval_value_uniq d₁c d₂c
      by contradiction

/-!
## 導出システムEvalML1Errのメタ定理

### 評価の（左）全域性：定理3.4 \[基礎概念,§3.2]
-/

/--
EvalML1Errの評価の（左）全域性（定理3.4・練習問題3.4 \[基礎概念,§3.2]）

\[基礎概念,小節3.2.2]で説明されているエラーの種類の識別を先取ったので、(2) $\MV{e}\Evals\TT{error}$を(2′) $\exists \MV{\varepsilon} \in \Set{Error}. \MV{e}\Evals\MV{\varepsilon}$と読み替えている。
-/
theorem eval_left_total (e : Expr) : (∃ v : Value, Derivable (e ⇓ v)) ∨ (∃ ε : Error, Derivable (e ⇓ ε)) :=
  let ⟨r, d⟩ := e.eval
  match r with
  | .inr v => .inl ⟨v, d⟩
  | .inl ε => .inr ⟨ε, d⟩

/-!
## 導出システムEvalML1Errのメタ定理

### 評価の（左）全域性：練習問題3.5 \[基礎概念,§3.2]
以下の3パターンに分けて、それぞれを補題として証明する：
- ${\MV{e}\Evals\MV{v\_1}} \land {\MV{e}\Evals\MV{v\_2}}$ ⟹ 定理3.2 `eval_value_uniq`
- ${\MV{e}\Evals\MV{v}} \land {\MV{e}\Evals\MV{\varepsilon}}$ ⟹ 補題`contra_eval_value_error`
- ${\MV{e}\Evals\MV{\varepsilon\_1}} \land {\MV{e}\Evals\MV{\varepsilon\_2}}$ ⟹ 補題`eval_error_uniq`
-/

/--
式$\MV{e}$を評価した結果が値にも実行時エラーにもなるということはない。
-/
theorem contra_eval_value_error : Derivation (e ⇓ .inr v₁) → Derivation (e ⇓ .inl ε₂) → False
  | .E_Plus  _   d₁r _, .E_PlusIntBool  _   d₂r => eval_value_uniq d₁r d₂r |> Value.noConfusion
  | .E_Plus  _   d₁r _, .E_PlusIntErr   _   d₂r => contra_eval_value_error d₁r d₂r
  | .E_Plus  d₁l _   _, .E_PlusBool     d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_Plus  d₁l _   _, .E_PlusErr      d₂l     => contra_eval_value_error d₁l d₂l
  | .E_Minus _   d₁r _, .E_MinusIntBool _   d₂r => eval_value_uniq d₁r d₂r |> Value.noConfusion
  | .E_Minus _   d₁r _, .E_MinusIntErr  _   d₂r => contra_eval_value_error d₁r d₂r
  | .E_Minus d₁l _   _, .E_MinusBool    d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_Minus d₁l _   _, .E_MinusErr     d₂l     => contra_eval_value_error d₁l d₂l
  | .E_Times _   d₁r _, .E_TimesIntBool _   d₂r => eval_value_uniq d₁r d₂r |> Value.noConfusion
  | .E_Times _   d₁r _, .E_TimesIntErr  _   d₂r => contra_eval_value_error d₁r d₂r
  | .E_Times d₁l _   _, .E_TimesBool    d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_Times d₁l _   _, .E_TimesErr     d₂l     => contra_eval_value_error d₁l d₂l
  | .E_LT    _   d₁r _, .E_LTIntBool    _   d₂r => eval_value_uniq d₁r d₂r |> Value.noConfusion
  | .E_LT    _   d₁r _, .E_LTIntErr     _   d₂r => contra_eval_value_error d₁r d₂r
  | .E_LT    d₁l _   _, .E_LTBool       d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_LT    d₁l _   _, .E_LTErr        d₂l     => contra_eval_value_error d₁l d₂l
  | .E_IfT   d₁c _    , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfT   d₁c _    , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c
  | .E_IfT   _   d₁t  , .E_IfTErr       _   d₂t => contra_eval_value_error d₁t d₂t
  | .E_IfT   d₁c _    , .E_IfFErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfF   d₁c _    , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfF   d₁c _    , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c
  | .E_IfF   _   d₁f  , .E_IfFErr       _   d₂t => contra_eval_value_error d₁f d₂t
  | .E_IfF   d₁c _    , .E_IfTErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion

/-!
補題`eval_error_uniq`はパターンが多いので実行時エラーの種類毎に補題として証明する。

各構文要素について
- その構文要素で発生する実行時エラーの導出
- 他の各構文要素から実行時エラーが伝播する導出

に対して一意性を示す。
導出の組み合わせによっては矛盾から示す場合もある。
-/

/--
加算の実行時エラーについての評価の一意性
-/
theorem eval_plus_error_uniq : Derivation (e ⇓ .inl Error.Plus) → Derivation (e ⇓ .inl ε) → Error.Plus = ε
  | .E_PlusIntBool  _   _  , .E_PlusIntBool   _   _   => rfl
  | .E_PlusIntBool  _   d₁r, .E_PlusIntErr    _   d₂r => contra_eval_value_error d₁r d₂r |> False.elim
  | .E_PlusIntBool  _   _  , .E_PlusBool      _       => rfl
  | .E_PlusIntBool  d₁l _  , .E_PlusErr       d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_PlusIntErr   _   _  , .E_PlusIntBool   _   _   => rfl
  | .E_PlusIntErr   _   d₁r, .E_PlusIntErr    _   d₂r => eval_plus_error_uniq d₁r d₂r
  | .E_PlusIntErr   _   _  , .E_PlusBool      _       => rfl
  | .E_PlusIntErr   d₁l _  , .E_PlusErr       d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_PlusBool     _      , .E_PlusIntBool   _   _   => rfl
  | .E_PlusBool     d₁l    , .E_PlusIntErr    d₂l _   => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_PlusBool     _      , .E_PlusBool      _       => rfl
  | .E_PlusBool     d₁l    , .E_PlusErr       d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_PlusErr      _      , .E_PlusIntBool   _   _   => rfl
  | .E_PlusErr      d₁l    , .E_PlusIntErr    d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      _      , .E_PlusBool      _       => rfl
  | .E_PlusErr      d₁l    , .E_PlusErr       d₂l     => eval_plus_error_uniq d₁l d₂l
  | .E_MinusIntErr  _   d₁r, .E_MinusIntBool  _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_MinusIntErr  _   d₁r, .E_MinusIntErr   _   d₂r => eval_plus_error_uniq d₁r d₂r
  | .E_MinusIntErr  d₁l _  , .E_MinusBool     d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_MinusIntErr  d₁l _  , .E_MinusErr      d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusIntBool  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusIntErr   d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusBool     d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusErr      d₂l     => eval_plus_error_uniq d₁l d₂l
  | .E_TimesIntErr  _   d₁r, .E_TimesIntBool  _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_TimesIntErr  _   d₁r, .E_TimesIntErr   _   d₂r => eval_plus_error_uniq d₁r d₂r
  | .E_TimesIntErr  d₁l _  , .E_TimesBool     d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_TimesIntErr  d₁l _  , .E_TimesErr      d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesIntBool  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesIntErr   d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesBool     d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesErr      d₂l     => eval_plus_error_uniq d₁l d₂l
  | .E_LTIntErr     _   d₁r, .E_LTIntBool     _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_LTIntErr     _   d₁r, .E_LTIntErr      _   d₂r => eval_plus_error_uniq d₁r d₂r
  | .E_LTIntErr     d₁l _  , .E_LTBool        d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_LTIntErr     d₁l _  , .E_LTErr         d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_LTErr        d₁l    , .E_LTIntBool     d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTIntErr      d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTBool        d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTErr         d₂l     => eval_plus_error_uniq d₁l d₂l
  | .E_IfCondErr    d₁c    , .E_IfCondInt     d₂c     => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfCondErr    d₁c    , .E_IfCondErr     d₂c     => eval_plus_error_uniq d₁c d₂c
  | .E_IfCondErr    d₁c    , .E_IfTErr        d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfCondErr    d₁c    , .E_IfFErr        d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfTErr       d₁c _  , .E_IfCondInt     d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfTErr       d₁c _  , .E_IfCondErr     d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfTErr       _   d₁t, .E_IfTErr        _   d₂t => eval_plus_error_uniq d₁t d₂t
  | .E_IfTErr       d₁c _  , .E_IfFErr        d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondInt     d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondErr     d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfFErr       d₁c _  , .E_IfTErr        d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       _   d₁t, .E_IfFErr        _   d₂t => eval_plus_error_uniq d₁t d₂t

/--
減算の実行時エラーについての評価の一意性
-/
theorem eval_minus_error_uniq : Derivation (e ⇓ .inl Error.Minus) → Derivation (e ⇓ .inl ε) → Error.Minus = ε
  | .E_PlusIntErr   _   d₁r, .E_PlusIntBool  _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_PlusIntErr   _   d₁r, .E_PlusIntErr   _   d₂r => eval_minus_error_uniq d₁r d₂r
  | .E_PlusIntErr   d₁l _  , .E_PlusBool     d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_PlusIntErr   d₁l _  , .E_PlusErr      d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusIntBool  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusIntErr   d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusBool     d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusErr      d₂l     => eval_minus_error_uniq d₁l d₂l
  | .E_MinusIntBool _   _  , .E_MinusIntBool _   _   => rfl
  | .E_MinusIntBool _   d₁r, .E_MinusIntErr  _   d₂r => contra_eval_value_error d₁r d₂r |> False.elim
  | .E_MinusIntBool _   _  , .E_MinusBool    _       => rfl
  | .E_MinusIntBool d₁l _  , .E_MinusErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_MinusIntErr  _   d₁r, .E_MinusIntBool _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_MinusIntErr  _   d₁r, .E_MinusIntErr  _   d₂r => eval_minus_error_uniq d₁r d₂r
  | .E_MinusIntErr  _   _  , .E_MinusBool    _       => rfl
  | .E_MinusIntErr  d₁l _  , .E_MinusErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_MinusBool    _      , .E_MinusIntBool _   _   => rfl
  | .E_MinusBool    d₁l    , .E_MinusIntErr  d₂l _   => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_MinusBool    _      , .E_MinusBool    _       => rfl
  | .E_MinusBool    d₁l    , .E_MinusErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_MinusErr     _      , .E_MinusIntBool _   _   => rfl
  | .E_MinusErr     d₁l    , .E_MinusIntErr  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     _      , .E_MinusBool    _       => rfl
  | .E_MinusErr     d₁l    , .E_MinusErr     d₂l     => eval_minus_error_uniq d₁l d₂l
  | .E_TimesIntErr  _   d₁r, .E_TimesIntBool _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_TimesIntErr  _   d₁r, .E_TimesIntErr  _   d₂r => eval_minus_error_uniq d₁r d₂r
  | .E_TimesIntErr  d₁l _  , .E_TimesBool    d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_TimesIntErr  d₁l _  , .E_TimesErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesIntBool d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesIntErr  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesBool    d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesErr     d₂l     => eval_minus_error_uniq d₁l d₂l
  | .E_LTIntErr     _   d₁r, .E_LTIntBool    _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_LTIntErr     _   d₁r, .E_LTIntErr     _   d₂r => eval_minus_error_uniq d₁r d₂r
  | .E_LTIntErr     d₁l _  , .E_LTBool       d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_LTIntErr     d₁l _  , .E_LTErr        d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_LTErr        d₁l    , .E_LTIntBool    d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTIntErr     d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTBool       d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTErr        d₂l     => eval_minus_error_uniq d₁l d₂l
  | .E_IfCondErr    d₁c    , .E_IfCondInt    d₂c     => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfCondErr    d₁c    , .E_IfCondErr    d₂c     => eval_minus_error_uniq d₁c d₂c
  | .E_IfCondErr    d₁c    , .E_IfTErr       d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfCondErr    d₁c    , .E_IfFErr       d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfTErr       d₁c _  , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfTErr       d₁c _  , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfTErr       _   d₁t, .E_IfTErr       _   d₂t => eval_minus_error_uniq d₁t d₂t
  | .E_IfTErr       d₁c _  , .E_IfFErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfFErr       d₁c _  , .E_IfTErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       _   d₁t, .E_IfFErr       _   d₂t => eval_minus_error_uniq d₁t d₂t

/--
乗算の実行時エラーについての評価の一意性
-/
theorem eval_times_error_uniq : Derivation (e ⇓ .inl Error.Times) → Derivation (e ⇓ .inl ε) → Error.Times = ε
  | .E_PlusIntErr   _   d₁r, .E_PlusIntBool  _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_PlusIntErr   _   d₁r, .E_PlusIntErr   _   d₂r => eval_times_error_uniq d₁r d₂r
  | .E_PlusIntErr   d₁l _  , .E_PlusBool     d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_PlusIntErr   d₁l _  , .E_PlusErr      d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusIntBool  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusIntErr   d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusBool     d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusErr      d₂l     => eval_times_error_uniq d₁l d₂l
  | .E_MinusIntErr  _   d₁r, .E_MinusIntBool _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_MinusIntErr  _   d₁r, .E_MinusIntErr  _   d₂r => eval_times_error_uniq d₁r d₂r
  | .E_MinusIntErr  d₁l _  , .E_MinusBool    d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_MinusIntErr  d₁l _  , .E_MinusErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusIntBool d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusIntErr  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusBool    d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusErr     d₂l     => eval_times_error_uniq d₁l d₂l
  | .E_TimesIntBool _   _  , .E_TimesIntBool _   _   => rfl
  | .E_TimesIntBool _   d₁r, .E_TimesIntErr  _   d₂r => contra_eval_value_error d₁r d₂r |> False.elim
  | .E_TimesIntBool _   _  , .E_TimesBool    _       => rfl
  | .E_TimesIntBool d₁l _  , .E_TimesErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_TimesIntErr  _   d₁r, .E_TimesIntBool _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_TimesIntErr  _   d₁r, .E_TimesIntErr  _   d₂r => eval_times_error_uniq d₁r d₂r
  | .E_TimesIntErr  _   _  , .E_TimesBool    _       => rfl
  | .E_TimesIntErr  d₁l _  , .E_TimesErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_TimesBool    _      , .E_TimesIntBool _   _   => rfl
  | .E_TimesBool    d₁l    , .E_TimesIntErr  d₂l _   => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_TimesBool    _      , .E_TimesBool    _       => rfl
  | .E_TimesBool    d₁l    , .E_TimesErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_TimesErr     _      , .E_TimesIntBool _   _   => rfl
  | .E_TimesErr     d₁l    , .E_TimesIntErr  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     _      , .E_TimesBool    _       => rfl
  | .E_TimesErr     d₁l    , .E_TimesErr     d₂l     => eval_times_error_uniq d₁l d₂l
  | .E_LTIntErr     _   d₁r, .E_LTIntBool    _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_LTIntErr     _   d₁r, .E_LTIntErr     _   d₂r => eval_times_error_uniq d₁r d₂r
  | .E_LTIntErr     d₁l _  , .E_LTBool       d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_LTIntErr     d₁l _  , .E_LTErr        d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_LTErr        d₁l    , .E_LTIntBool    d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTIntErr     d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTBool       d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTErr        d₂l     => eval_times_error_uniq d₁l d₂l
  | .E_IfCondErr    d₁c    , .E_IfCondInt    d₂c     => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfCondErr    d₁c    , .E_IfCondErr    d₂c     => eval_times_error_uniq d₁c d₂c
  | .E_IfCondErr    d₁c    , .E_IfTErr       d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfCondErr    d₁c    , .E_IfFErr       d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfTErr       d₁c _  , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfTErr       d₁c _  , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfTErr       _   d₁t, .E_IfTErr       _   d₂t => eval_times_error_uniq d₁t d₂t
  | .E_IfTErr       d₁c _  , .E_IfFErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfFErr       d₁c _  , .E_IfTErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       _   d₁t, .E_IfFErr       _   d₂t => eval_times_error_uniq d₁t d₂t

/--
小なり比較の実行時エラーについての評価の一意性
-/
theorem eval_lt_error_uniq : Derivation (e ⇓ .inl Error.LT) → Derivation (e ⇓ .inl ε) → Error.LT = ε
  | .E_PlusIntErr   _   d₁r, .E_PlusIntBool  _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_PlusIntErr   _   d₁r, .E_PlusIntErr   _   d₂r => eval_lt_error_uniq d₁r d₂r
  | .E_PlusIntErr   d₁l _  , .E_PlusBool     d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_PlusIntErr   d₁l _  , .E_PlusErr      d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusIntBool  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusIntErr   d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusBool     d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusErr      d₂l     => eval_lt_error_uniq d₁l d₂l
  | .E_MinusIntErr  _   d₁r, .E_MinusIntBool _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_MinusIntErr  _   d₁r, .E_MinusIntErr  _   d₂r => eval_lt_error_uniq d₁r d₂r
  | .E_MinusIntErr  d₁l _  , .E_MinusBool    d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_MinusIntErr  d₁l _  , .E_MinusErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusIntBool d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusIntErr  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusBool    d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusErr     d₂l     => eval_lt_error_uniq d₁l d₂l
  | .E_TimesIntErr  _   d₁r, .E_TimesIntBool _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_TimesIntErr  _   d₁r, .E_TimesIntErr  _   d₂r => eval_lt_error_uniq d₁r d₂r
  | .E_TimesIntErr  d₁l _  , .E_TimesBool    d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_TimesIntErr  d₁l _  , .E_TimesErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesIntBool d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesIntErr  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesBool    d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesErr     d₂l     => eval_lt_error_uniq d₁l d₂l
  | .E_LTIntBool    _   _  , .E_LTIntBool    _   _   => rfl
  | .E_LTIntBool    _   d₁r, .E_LTIntErr     _   d₂r => contra_eval_value_error d₁r d₂r |> False.elim
  | .E_LTIntBool    _   _  , .E_LTBool       _       => rfl
  | .E_LTIntBool    d₁l _  , .E_LTErr        d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_LTIntErr     _   _  , .E_LTIntBool    _   _   => rfl
  | .E_LTIntErr     _   d₁r, .E_LTIntErr     _   d₂r => eval_lt_error_uniq d₁r d₂r
  | .E_LTIntErr     _   _  , .E_LTBool       _       => rfl
  | .E_LTIntErr     d₁l _  , .E_LTErr        d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_LTBool       _      , .E_LTIntBool    _   _   => rfl
  | .E_LTBool       d₁l    , .E_LTIntErr     d₂l _   => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_LTBool       _      , .E_LTBool       _       => rfl
  | .E_LTBool       d₁l    , .E_LTErr        d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_LTErr        _      , .E_LTIntBool    _   _   => rfl
  | .E_LTErr        d₁l    , .E_LTIntErr     d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        _      , .E_LTBool       _       => rfl
  | .E_LTErr        d₁l    , .E_LTErr        d₂l     => eval_lt_error_uniq d₁l d₂l
  | .E_IfCondErr    d₁c    , .E_IfCondInt    d₂c     => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfCondErr    d₁c    , .E_IfCondErr    d₂c     => eval_lt_error_uniq d₁c d₂c
  | .E_IfCondErr    d₁c    , .E_IfTErr       d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfCondErr    d₁c    , .E_IfFErr       d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfTErr       d₁c _  , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfTErr       d₁c _  , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfTErr       _   d₁t, .E_IfTErr       _   d₂t => eval_lt_error_uniq d₁t d₂t
  | .E_IfTErr       d₁c _  , .E_IfFErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfFErr       d₁c _  , .E_IfTErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       _   d₁t, .E_IfFErr       _   d₂t => eval_lt_error_uniq d₁t d₂t

/--
条件分岐の条件式の実行時エラーについての評価の一意性
-/
theorem eval_if_cond_error_uniq : Derivation (e ⇓ .inl Error.IfCond) → Derivation (e ⇓ .inl ε) → Error.IfCond = ε
  | .E_PlusIntErr   _   d₁r, .E_PlusIntBool  _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_PlusIntErr   _   d₁r, .E_PlusIntErr   _   d₂r => eval_if_cond_error_uniq d₁r d₂r
  | .E_PlusIntErr   d₁l _  , .E_PlusBool     d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_PlusIntErr   d₁l _  , .E_PlusErr      d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusIntBool  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusIntErr   d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusBool     d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_PlusErr      d₁l    , .E_PlusErr      d₂l     => eval_if_cond_error_uniq d₁l d₂l
  | .E_MinusIntErr  _   d₁r, .E_MinusIntBool _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_MinusIntErr  _   d₁r, .E_MinusIntErr  _   d₂r => eval_if_cond_error_uniq d₁r d₂r
  | .E_MinusIntErr  d₁l _  , .E_MinusBool    d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_MinusIntErr  d₁l _  , .E_MinusErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusIntBool d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusIntErr  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusBool    d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_MinusErr     d₁l    , .E_MinusErr     d₂l     => eval_if_cond_error_uniq d₁l d₂l
  | .E_TimesIntErr  _   d₁r, .E_TimesIntBool _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_TimesIntErr  _   d₁r, .E_TimesIntErr  _   d₂r => eval_if_cond_error_uniq d₁r d₂r
  | .E_TimesIntErr  d₁l _  , .E_TimesBool    d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_TimesIntErr  d₁l _  , .E_TimesErr     d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesIntBool d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesIntErr  d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesBool    d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_TimesErr     d₁l    , .E_TimesErr     d₂l     => eval_if_cond_error_uniq d₁l d₂l
  | .E_LTIntErr     _   d₁r, .E_LTIntBool    _   d₂r => contra_eval_value_error d₂r d₁r |> False.elim
  | .E_LTIntErr     _   d₁r, .E_LTIntErr     _   d₂r => eval_if_cond_error_uniq d₁r d₂r
  | .E_LTIntErr     d₁l _  , .E_LTBool       d₂l     => eval_value_uniq d₁l d₂l |> Value.noConfusion
  | .E_LTIntErr     d₁l _  , .E_LTErr        d₂l     => contra_eval_value_error d₁l d₂l |> False.elim
  | .E_LTErr        d₁l    , .E_LTIntBool    d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTIntErr     d₂l _   => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTBool       d₂l     => contra_eval_value_error d₂l d₁l |> False.elim
  | .E_LTErr        d₁l    , .E_LTErr        d₂l     => eval_if_cond_error_uniq d₁l d₂l
  | .E_IfCondInt    _      , .E_IfCondInt    _       => rfl
  | .E_IfCondInt    d₁c    , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfCondInt    d₁c    , .E_IfTErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfCondInt    d₁c    , .E_IfFErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfCondErr    _      , .E_IfCondInt    _       => rfl
  | .E_IfCondErr    d₁c    , .E_IfCondErr    d₂c     => eval_if_cond_error_uniq d₁c d₂c
  | .E_IfCondErr    d₁c    , .E_IfTErr       d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfCondErr    d₁c    , .E_IfFErr       d₂c _   => contra_eval_value_error d₂c d₁c |> False.elim
  | .E_IfTErr       d₁c _  , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfTErr       d₁c _  , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfTErr       _   d₁t, .E_IfTErr       _   d₂t => eval_if_cond_error_uniq d₁t d₂t
  | .E_IfTErr       d₁c _  , .E_IfFErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondInt    d₂c     => eval_value_uniq d₁c d₂c |> Value.noConfusion
  | .E_IfFErr       d₁c _  , .E_IfCondErr    d₂c     => contra_eval_value_error d₁c d₂c |> False.elim
  | .E_IfFErr       d₁c _  , .E_IfTErr       d₂c _   => eval_value_uniq d₁c d₂c |> Value.B.inj |> Bool.noConfusion
  | .E_IfFErr       _   d₁t, .E_IfFErr       _   d₂t => eval_if_cond_error_uniq d₁t d₂t

/--
実行時エラーに関する評価の一意性
-/
theorem eval_error_uniq : {ε₁ : Error} → Derivation (e ⇓ .inl ε₁) → Derivation (e ⇓ .inl ε₂) → ε₁ = ε₂
  | .Plus   => eval_plus_error_uniq
  | .Minus  => eval_minus_error_uniq
  | .Times  => eval_times_error_uniq
  | .LT     => eval_lt_error_uniq
  | .IfCond => eval_if_cond_error_uniq

/-!
以上の補題をまとめ上げる。
-/

/--
EvalML1Errの評価の一意性（練習問題3.5 \[基礎概念,§3.2]）
-/
theorem eval_uniq {e : Expr} : {r₁ r₂ : Result} → Derivation (e ⇓ r₁) → Derivation (e ⇓ r₂) → r₁ = r₂
  | .inr _, .inr _ => fun d₁ d₂ => congrArg Sum.inr <| eval_value_uniq d₁ d₂
  | .inr _, .inl _ => fun d₁ d₂ => False.elim <| contra_eval_value_error d₁ d₂
  | .inl _, .inr _ => fun d₁ d₂ => False.elim <| contra_eval_value_error d₂ d₁
  | .inl _, .inl _ => fun d₁ d₂ => congrArg Sum.inl <| eval_error_uniq d₁ d₂
