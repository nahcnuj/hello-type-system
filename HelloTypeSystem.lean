-- This module serves as the root of the `HelloTypeSystem` library.
-- Import modules here that should be built as part of the library.
import «HelloTypeSystem».Basic
import «HelloTypeSystem».Meta
import «HelloTypeSystem».ML1
/-!
$\newcommand\Set[1]{\mathbf{#1}}$
$\newcommand\MV[1]{\boldsymbol{#1}}$
$\newcommand\TT[1]{\texttt{#1}}$
$\newcommand\Evals{\mathrel{\Downarrow}}$
$\newcommand\Reduces{\mathrel{\longrightarrow}}$
$\newcommand\MReduces{\mathrel{\longrightarrow^{\\!*}}}$
$\newcommand\DReduces{\mathrel{\longrightarrow_{\\!d}}}$
-/

/-!
# Hello, Type System
Lean 4でプログラミング言語の型システムや意味論に入門するリポジトリです。

## Index
- [諸定義](./HelloTypeSystem/Basic.html)
  - ペアノ自然数
  - 算術式
  - 判断（judgement）
  - 導出システム（derivation systems）
    - PeanoNat：ペアノ自然数の加算・乗算 \[基礎概念,§1.1]
    - CompareNat1--3：ペアノ自然数の比較 \[基礎概念,§1.3]
    - EvalNatExpr：算術式の評価 \[基礎概念,§1.4]
    - ReduceNatExpr：算術式の簡約 \[基礎概念,§1.4]
- ML言語の評価
  - [ML1](./HelloTypeSystem/ML1.html)：整数・真偽値式の評価 \[基礎概念,§3.1]
- 導出システムに関する主なメタ定理
  - PeanoNat
    - 加算：$\TT{$\MV{n_1}$ plus $\MV{n_2}$ is $\MV{n_3}$}$
      - 左全域性：`HelloTypeSystem.PeanoNat.derive_plus`
      - 一意性：`HelloTypeSystem.PeanoNat.plus_uniq`
      - 可換律：`HelloTypeSystem.PeanoNat.plus_comm`
      - [結合律](./HelloTypeSystem/Meta/PeanoNat.html#定理2-5)
    - 乗算：$\TT{$\MV{n_1}$ times $\MV{n_2}$ is $\MV{n_3}$}$
      - 左全域性：`HelloTypeSystem.PeanoNat.derive_times`
      - 一意性：`HelloTypeSystem.PeanoNat.times_uniq`
      - 可換律：`HelloTypeSystem.PeanoNat.times_comm`
      - [結合律](./HelloTypeSystem/Meta/PeanoNat.html#定理2-10)
  - CompareNat1--3
    - 比較${}<{}$
      - [推移律](./HelloTypeSystem/Meta/CompareNat.html#定理2-13-推移律-基礎概念-2-1)
    - 3つの導出システムの[同値性](./HelloTypeSystem/Meta/CompareNat.html#定理2-14-基礎概念-2-1)
  - EvalNatExpr
    - [PeanoNatの判断を含むこと](./HelloTypeSystem/Meta/EvalNatExpr.html#EvalNatExprがNatの導出を含むこと)
    - 評価${}\Evals{}$
      - 左全域性 `HelloTypeSystem.EvalNatExpr.eval_left_total`
      - 一意性 `HelloTypeSystem.EvalNatExpr.eval_uniq`
      - ${\MV{e}\Evals\MV{n}} \implies {\MV{e}\MReduces\MV{n}}$ `HelloTypeSystem.mreduce_of_eval`
  - ReduceNatExpr
    - 簡約${}\Reduces{},{}\MReduces{}$
      - 前進性 `HelloTypeSystem.ReduceNatExpr.reduce_progressive`
      - 合流性 `HelloTypeSystem.ReduceNatExpr.reduce_confluence`
      - ${\MV{e}\MReduces\MV{n}} \implies {\MV{e}\Evals\MV{n}}$ `HelloTypeSystem.eval_of_mreduce`
      - 弱正規化可能性 `HelloTypeSystem.ReduceNatExpr.weak_normalization`
    - 決定的簡約${}\DReduces{}$
      - 一意性 `HelloTypeSystem.ReduceNatExpr.dreduce_uniq`
  - EvalML1
    - 評価の一意性 `HelloTypeSystem.ML1.eval_uniq`

## Notation
- $\MV{n},\MV{n_1},\dots$（太字斜体）：メタ変数。特にペアノ自然数の場合はそれに対応する普通の自然数を$n,n_1,\dots$と書く。
- $\Set{PNat},\Set{Expr},\dots$（太字立体）：BNFで定義された構文要素の集合

## References
- `[基礎概念]`: 五十嵐淳 著. プログラミング言語の基礎概念, サイエンス社, 2011.7, (ライブラリ情報学コア・テキスト ; 24). 978-4-7819-1285-1. [https://ndlsearch.ndl.go.jp/books/R100000002-I000011238587](https://ndlsearch.ndl.go.jp/books/R100000002-I000011238587)
- `[基礎理論]`: 大堀淳 著. プログラミング言語の基礎理論. 新装版, 共立出版, 2019.8. 978-4-320-12450-9. [https://ndlsearch.ndl.go.jp/books/R100000002-I029842615](https://ndlsearch.ndl.go.jp/books/R100000002-I029842615)
- `[意味論入門]`: G.ウィンスケル 著ほか. プログラミング言語の形式的意味論入門, 丸善出版, 2023.1. 978-4-621-30763-2. [https://ndlsearch.ndl.go.jp/books/R100000002-I032600297](https://ndlsearch.ndl.go.jp/books/R100000002-I032600297)
-/
